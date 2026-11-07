import EvmOpt
import EvmOpt.Asm

open EvmOpt EvmSemantics EvmSemantics.EVM

def showItems (is : List Item) : String := " ".intercalate (is.map Item.show)

def optimizeFile (f : Fork) (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  for line in (text.splitOn "\n").filter (·.trimAscii.toString ≠ "") do
    let items := parseBlock line
    let out := optimizeItems f items
    IO.println s!"in:  {showItems items}"
    IO.println s!"out: {showItems out}"
    IO.println s!"gas (stack-only part): {itemsCost f items} -> {itemsCost f out}; \
      bytes: {itemsSize items} -> {itemsSize out}"

def checkPair (f : Fork) (a b : String) : IO UInt32 := do
  let parse (s : String) : Option Block :=
    (parseBlock s).mapM fun | .ins i => some i | .other _ => none
  match parse a, parse b with
  | some x, some y =>
    let ok := check f x y
    IO.println s!"check: {ok} (gas {cost f x} -> {cost f y})"
    return if ok then 0 else 1
  | _, _ =>
    IO.eprintln "both blocks must consist of supported stack instructions only"
    return 2

def main (args : List String) : IO UInt32 := do
  let f : Fork := .Cancun
  match args with
  | ["opt", path] => optimizeFile f path; return 0
  | ["check", a, b] => checkPair f a b
  | _ =>
    IO.eprintln "usage: evmopt opt <blocks.txt> | evmopt check \"<orig>\" \"<candidate>\""
    return 2
