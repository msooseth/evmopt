import EvmOpt.XOpt

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- An assembly item: a supported instruction, an assembler constant (`PUSH [tag] 5`, …,
    kept as text), or anything else (kept verbatim; a barrier). -/
inductive Item
  | ins (i : XInstr)
  | ptag (s : String)
  | other (s : String)
  deriving Repr, Inhabited

def arithNames : List (String × ArithOp) :=
  [("ADD", .ADD), ("MUL", .MUL), ("SUB", .SUB), ("DIV", .DIV), ("SDIV", .SDIV), ("MOD", .MOD),
   ("SMOD", .SMOD), ("ADDMOD", .ADDMOD), ("MULMOD", .MULMOD), ("SIGNEXTEND", .SIGNEXTEND),
   ("LT", .LT), ("GT", .GT), ("SLT", .SLT), ("SGT", .SGT), ("EQ", .EQ), ("ISZERO", .ISZERO),
   ("AND", .AND), ("OR", .OR), ("XOR", .XOR), ("NOT", .NOT), ("BYTE", .BYTE), ("SHL", .SHL),
   ("SHR", .SHR), ("SAR", .SAR), ("CLZ", .CLZ)]

def envNames : List (String × EnvOp) :=
  [("ADDRESS", .ADDRESS), ("ORIGIN", .ORIGIN), ("CALLER", .CALLER), ("CALLVALUE", .CALLVALUE),
   ("CALLDATALOAD", .CALLDATALOAD), ("CALLDATASIZE", .CALLDATASIZE), ("GASPRICE", .GASPRICE),
   ("RETURNDATASIZE", .RETURNDATASIZE), ("BLOCKHASH", .BLOCKHASH), ("COINBASE", .COINBASE),
   ("TIMESTAMP", .TIMESTAMP), ("NUMBER", .NUMBER), ("PREVRANDAO", .PREVRANDAO),
   ("DIFFICULTY", .PREVRANDAO), ("GASLIMIT", .GASLIMIT), ("CHAINID", .CHAINID),
   ("SELFBALANCE", .SELFBALANCE), ("BASEFEE", .BASEFEE)]

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseNum (s : String) : Option Nat :=
  if s.startsWith "0x" || s.startsWith "0X" then
    (s.toList.drop 2).foldlM (fun acc c => (hexDigit c).map (acc * 16 + ·)) 0
  else s.toNat?

/-- `n` as exactly `k` big-endian bytes, if it fits. -/
def fixedBytes (k n : Nat) : Option (List UInt8) :=
  if n < 256 ^ k then some ((List.range k).reverse.map fun j => ((n / 256 ^ j) % 256).toUInt8)
  else none

def opName? (s : String) : Option Instr :=
  if s = "POP" then some .pop
  else if s.startsWith "DUP" then
    (String.ofList (s.toList.drop 3)).toNat?.bind fun n =>
      if h : 1 ≤ n ∧ n ≤ 16 then some (.dup ⟨n - 1, by omega⟩) else none
  else if s.startsWith "SWAP" then
    (String.ofList (s.toList.drop 4)).toNat?.bind fun n =>
      if h : 1 ≤ n ∧ n ≤ 16 then some (.swap ⟨n - 1, by omega⟩) else none
  else match arithNames.lookup s with
    | some o => some (.op o)
    | none => (envNames.lookup s).map .env

/-- Effect ops handled in blocks (TSTORE stays a barrier: not handled symbolically). -/
def memNames : List (String × MemOp) :=
  [("MLOAD", .MLOAD), ("MSTORE", .MSTORE), ("MSTORE8", .MSTORE8), ("SLOAD", .SLOAD),
   ("TLOAD", .TLOAD), ("KECCAK256", .KECCAK256), ("SHA3", .KECCAK256)]

def xopName? (s : String) : Option XInstr :=
  match opName? s with
  | some i => some (.base i)
  | none => (memNames.lookup s).map .mem

def pseudoPushArgs : List String := ["[tag]", "#[$]", "[$]", "data", "$"]

mutual
/-- solc-asm style `PUSH v` (hex without `0x`, minimal width). -/
partial def pushAsm (v : String) (rest : List String) : List Item :=
  match parseNum (if v.startsWith "0x" then v else "0x" ++ v) with
  | some n =>
    let bs := natBytes n
    if bs.length ≤ 32 then .ins (.base (.push (if bs.isEmpty then [0] else bs))) :: parseTokens rest
    else .other s!"PUSH {v}" :: parseTokens rest
  | none => .other s!"PUSH {v}" :: parseTokens rest

partial def parseTokens : List String → List Item
  | [] => []
  | "PUSH0" :: rest => .ins (.base (.push [])) :: parseTokens rest
  | "PUSH" :: kind :: v :: rest =>
    if pseudoPushArgs.contains kind then .ptag s!"PUSH {kind} {v}" :: parseTokens rest
    else pushAsm kind (v :: rest)
  | ["PUSH", v] => pushAsm v []
  | t :: rest =>
    if t.startsWith "PUSH" then
      match (String.ofList (t.toList.drop 4)).toNat?, rest with
      | some k, v :: rest' =>
        match parseNum v >>= fixedBytes k with
        | some bs => if 1 ≤ k ∧ k ≤ 32 then .ins (.base (.push bs)) :: parseTokens rest'
                     else .other s!"{t} {v}" :: parseTokens rest'
        | none => .other s!"{t} {v}" :: parseTokens rest'
      | _, _ => .other t :: parseTokens rest
    else match xopName? t with
      | some i => .ins i :: parseTokens rest
      | none => .other t :: parseTokens rest
end

def parseBlock (s : String) : List Item :=
  parseTokens (s.splitOn " " |>.flatMap (·.splitOn "\n") |>.flatMap (·.splitOn "\t")
    |>.map (·.trimAscii.toString) |>.filter (· ≠ ""))

def hexByte (b : UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!]

def Instr.show : Instr → String
  | .push [] => "PUSH0"
  | .push bs => s!"PUSH{bs.length} 0x" ++ String.join (bs.map hexByte)
  | .dup n => s!"DUP{n.val + 1}"
  | .swap n => s!"SWAP{n.val + 1}"
  | .pop => "POP"
  | .op o => ((arithNames.find? (·.2 == o)).map (·.1)).getD "?"
  | .env e => ((envNames.find? (·.2 == e)).map (·.1)).getD "?"

def XInstr.show : XInstr → String
  | .base i => i.show
  | .mem m => ((memNames.find? (·.2 == m)).map (·.1)).getD "?"
  | .tag k => s!"PUSH [tag?] {k}"

def Item.show : Item → String
  | .ins i => i.show
  | .ptag s => s
  | .other s => s

/-- Number assembler constants by their text: equal text, equal tag. -/
def tagItems (tbl : List String) (items : List Item) : Option (XBlock × List String) :=
  items.foldlM (fun (b, t) it => match it with
    | .ins x => some (b ++ [x], t)
    | .ptag s => match t.idxOf? s with
      | some k => some (b ++ [.tag k], t)
      | none => some (b ++ [.tag t.length], t ++ [s])
    | .other _ => none) ([], tbl)

def untag (tbl : List String) (b : XBlock) : List Item :=
  b.map fun | .tag k => .ptag (tbl.getD k "PUSH ?") | x => .ins x

/-- Maximal runs of supported instructions and assembler constants, separated by barriers. -/
def runs : List Item → List (Sum (List Item) String)
  | [] => []
  | .other s :: rest => .inr s :: runs rest
  | it :: rest =>
    match runs rest with
    | .inl b :: more => .inl (it :: b) :: more
    | more => .inl [it] :: more

def optimizeItems (f : Fork) (items : List Item) : List Item :=
  (runs items).flatMap fun
    | .inl r => match tagItems [] r with
      | some (b, tbl) => untag tbl (optimizeX f b)
      | none => r
    | .inr s => [.other s]

def itemsCost (f : Fork) (items : List Item) : Nat :=
  (runs items).foldl (fun acc r => match r with
    | .inl r => acc + ((tagItems [] r).map (xcost f ·.1)).getD 0
    | .inr _ => acc) 0

def itemsSize (items : List Item) : Nat :=
  items.foldl (fun acc i => match i with
    | .ins i => acc + i.size | .ptag _ => acc + 3 | .other _ => acc) 0

end EvmOpt
