import EvmOpt.Search

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

/-- An assembly item: a supported straight-line instruction, or anything else (kept verbatim
    and treated as a barrier). -/
inductive Item
  | ins (i : Instr)
  | other (s : String)
  deriving Repr, Inhabited

def arithNames : List (String × ArithOp) :=
  [("ADD", .ADD), ("MUL", .MUL), ("SUB", .SUB), ("DIV", .DIV), ("SDIV", .SDIV), ("MOD", .MOD),
   ("SMOD", .SMOD), ("ADDMOD", .ADDMOD), ("MULMOD", .MULMOD), ("SIGNEXTEND", .SIGNEXTEND),
   ("LT", .LT), ("GT", .GT), ("SLT", .SLT), ("SGT", .SGT), ("EQ", .EQ), ("ISZERO", .ISZERO),
   ("AND", .AND), ("OR", .OR), ("XOR", .XOR), ("NOT", .NOT), ("BYTE", .BYTE), ("SHL", .SHL),
   ("SHR", .SHR), ("SAR", .SAR), ("CLZ", .CLZ)]

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
  else (arithNames.lookup s).map .op

def pseudoPushArgs : List String := ["[tag]", "#[$]", "[$]", "data", "$"]

mutual
/-- solc-asm style `PUSH v` (hex without `0x`, minimal width). -/
partial def pushAsm (v : String) (rest : List String) : List Item :=
  match parseNum (if v.startsWith "0x" then v else "0x" ++ v) with
  | some n =>
    let bs := natBytes n
    if bs.length ≤ 32 then .ins (.push (if bs.isEmpty then [0] else bs)) :: parseTokens rest
    else .other s!"PUSH {v}" :: parseTokens rest
  | none => .other s!"PUSH {v}" :: parseTokens rest

partial def parseTokens : List String → List Item
  | [] => []
  | "PUSH0" :: rest => .ins (.push []) :: parseTokens rest
  | "PUSH" :: kind :: v :: rest =>
    if pseudoPushArgs.contains kind then .other s!"PUSH {kind} {v}" :: parseTokens rest
    else pushAsm kind (v :: rest)
  | ["PUSH", v] => pushAsm v []
  | t :: rest =>
    if t.startsWith "PUSH" then
      match (String.ofList (t.toList.drop 4)).toNat?, rest with
      | some k, v :: rest' =>
        match parseNum v >>= fixedBytes k with
        | some bs => if 1 ≤ k ∧ k ≤ 32 then .ins (.push bs) :: parseTokens rest'
                     else .other s!"{t} {v}" :: parseTokens rest'
        | none => .other s!"{t} {v}" :: parseTokens rest'
      | _, _ => .other t :: parseTokens rest
    else match opName? t with
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

def Item.show : Item → String
  | .ins i => i.show
  | .other s => s

/-- Maximal runs of supported instructions, separated by barriers. -/
def runs : List Item → List (Sum Block String)
  | [] => []
  | .other s :: rest => .inr s :: runs rest
  | .ins i :: rest =>
    match runs rest with
    | .inl b :: more => .inl (i :: b) :: more
    | more => .inl [i] :: more

def optimizeItems (f : Fork) (items : List Item) : List Item :=
  (runs items).flatMap fun
    | .inl b => (optimizeBlock f b).map .ins
    | .inr s => [.other s]

def itemsCost (f : Fork) (items : List Item) : Nat :=
  (runs items).foldl (fun acc r => match r with | .inl b => acc + cost f b | .inr _ => acc) 0

def itemsSize (items : List Item) : Nat :=
  items.foldl (fun acc i => match i with | .ins i => acc + i.size | .other _ => acc) 0

end EvmOpt
