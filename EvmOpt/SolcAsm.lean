import Lean.Data.Json
import EvmOpt.Asm

namespace EvmOpt
open Lean EvmSemantics EvmSemantics.EVM

/-- One solc `--combined-json asm` item. `PUSH v` gets the minimal width (solc's assembler
    does the same); `PUSH 0` is `PUSH1 0` unless the fork has PUSH0. -/
def solcItem (f : Fork) (j : Json) : Item :=
  let name := (j.getObjValAs? String "name").toOption.getD "?"
  let value := (j.getObjValAs? String "value").toOption
  if name = "PUSH" then
    match value.bind (fun v => parseNum ("0x" ++ v)) with
    | some n =>
      let bs := natBytes n
      if bs.length ≤ 32 then
        .ins (.base (.push (if bs.isEmpty && !push0Ok f then [0] else bs)))
      else .other s!"PUSH {value.getD ""}"
    | none => .other s!"PUSH {value.getD ""}"
  else if name = "PUSH0" then .ins (.base (.push []))
  else match xopName? name, value with
    | some i, none => .ins i
    | _, some v => .other s!"{name} {v}"
    | _, none => .other name

partial def collectCodes (j : Json) : List (Array Json) :=
  let here := match j.getObjValAs? (Array Json) ".code" with
    | .ok c => [c]
    | .error _ => []
  let sub := match j.getObjVal? ".data" with
    | .ok (.obj kvs) => kvs.toList.flatMap fun (_, v) => collectCodes v
    | _ => []
  here ++ sub

/-- Codes per contract, keyed by `file.sol:Contract` (path prefix dropped). -/
def contractCodes (j : Json) : List (String × List (Array Json)) :=
  match j.getObjVal? "contracts" with
  | .ok (.obj kvs) => kvs.toList.map fun (name, c) =>
    ((name.splitOn "/").getLast!, match c.getObjVal? "asm" with
      | .ok a => collectCodes a
      | .error _ => [])
  | _ => []

def endsBlock (s : String) : Bool :=
  ["JUMP", "JUMPI", "STOP", "RETURN", "REVERT", "INVALID", "SELFDESTRUCT"].contains s

def startsBlock (s : String) : Bool := s.startsWith "tag" || s == "JUMPDEST"

/-- Split at control flow: tags/JUMPDESTs start a block, jumps and halts end one. -/
def splitBlocks (items : List Item) : List (List Item) :=
  let step := fun (acc : List (List Item) × List Item) (it : Item) =>
    let (done, cur) := acc
    match it with
    | .other s =>
      if startsBlock s then
        ((if cur.isEmpty then done else cur.reverse :: done), [it])
      else if endsBlock s then ((it :: cur).reverse :: done, [])
      else (done, it :: cur)
    | .ins _ => (done, it :: cur)
  let (done, cur) := items.foldl step ([], [])
  (if cur.isEmpty then done else cur.reverse :: done).reverse

def stackOnly (b : List Item) : Option Block :=
  b.mapM fun | .ins (.base i) => some i | _ => none

def effectBlock (b : List Item) : Option XBlock :=
  b.mapM fun | .ins x => some x | .other _ => none

/-- Strip a leading tag/JUMPDEST and trailing jump/halt so the stack-only body remains. -/
def body (b : List Item) : List Item :=
  let b := b.dropWhile fun | .other s => startsBlock s | _ => false
  (b.reverse.dropWhile fun | .other s => endsBlock s || s.startsWith "PUSH [tag]" | _ => false).reverse

/-- Why `check` rejected, for the report. -/
def checkReason (f : Fork) (b b' : Block) : String :=
  match lift f b, lift f b' with
  | none, _ => "original not liftable"
  | _, none => "candidate not liftable"
  | some S, some S' =>
    if S'.d > S.d then s!"candidate reads deeper ({S'.d} > {S.d})"
    else if S.slack + ((S.d : Int) - S'.d) > S'.slack then "candidate needs more stack room"
    else if cost f b' > cost f b then s!"candidate costs more ({cost f b'} > {cost f b})"
    else "terms differ after normalisation"

def mix (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def interesting : Array Nat :=
  #[0, 1, 2, 3, 31, 32, 255, 256, 2 ^ 160 - 1, 2 ^ 255, 2 ^ 256 - 1, 2 ^ 256 - 2]

def randWord (seed : UInt64) : UInt256 :=
  let s1 := mix seed
  if s1 % 3 == 0 then UInt256.ofNat interesting[(s1 >>> 8).toNat % interesting.size]!
  else
    let s2 := mix s1; let s3 := mix s2; let s4 := mix s3
    UInt256.ofNat (s1.toNat + s2.toNat * 2 ^ 64 + s3.toNat * 2 ^ 128 + s4.toNat * 2 ^ 192)

def randStack (seed : UInt64) (n : Nat) : List UInt256 :=
  (List.range n).map fun i => randWord (mix (seed + UInt64.ofNat (i * 7919 + 1)))

/-- A concrete input on which `b` succeeds but `b'` does not produce the same stack. -/
def counterexample (f : Fork) (b b' : Block) (tries : Nat := 300) :
    Option (List UInt256 × List UInt256 × Option (List UInt256)) :=
  (List.range tries).findSome? fun t =>
    let stk := randStack (UInt64.ofNat (t * 104729 + 17)) 40
    match run f default b stk with
    | some r => if run f default b' stk = some r then none else some (stk, r, run f default b' stk)
    | none => none

end EvmOpt
