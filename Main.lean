import EvmOpt
import EvmOpt.Asm
import EvmOpt.SolcAsm

open EvmOpt EvmSemantics EvmSemantics.EVM

def showItems (is : List Item) : String := " ".intercalate (is.map Item.show)

def optimizeFile (f : Fork) (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  for line in (text.splitOn "\n").filter (·.trimAscii.toString ≠ "") do
    let items := parseBlock line
    let out := optimizeItems f items
    IO.println s!"in:  {showItems items}"
    IO.println s!"out: {showItems out}"
    IO.println s!"     gas {itemsCost f items} -> {itemsCost f out}, \
      bytes {itemsSize items} -> {itemsSize out}"

def hexWord (v : UInt256) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 v.toNat)

/-- Is `cand` a correct (and no more expensive) replacement for `orig`? -/
def verifyPair (f : Fork) (a b : String) : IO UInt32 := do
  let pa := tagItems [] (parseBlock a)
  let pb := pa.bind fun (_, tbl) => tagItems tbl (parseBlock b)
  match pa.map (·.1), pb.map (·.1) with
  | some x, some y =>
    let ok := xcheck f x y
    if ok then
      IO.println s!"verified: equivalent, gas {xcost f x} -> {xcost f y}"
      return 0
    IO.println s!"rejected: {xcheckReason f x y}"
    let hasTag := (x ++ y).any (· matches .tag _)
    -- show only the inputs the original reads and the outputs it produces
    let (din, dout) := ((xlift f x).map fun X => (X.S.d, X.S.ts.length)).getD (4, 4)
    let shw := fun (n : Nat) (l : List UInt256) =>
      "[" ++ ", ".intercalate ((l.take n).map hexWord) ++ "]"
    match x.mapM XInstr.base?, y.mapM XInstr.base? with
    | some bx, some by_ =>
      match counterexample f bx by_ with
      | some (stk, r, r') =>
        IO.println s!"  counterexample: input stack (top first) {shw din stk}"
        IO.println s!"    original  -> {shw dout r}"
        IO.println s!"    candidate -> {(r'.map (shw dout)).getD "fails"}"
      | none => IO.println "  (no concrete counterexample found)"
    | _, _ =>
      match (if hasTag then none else xcounterexample f x y) with
      | some (what, stk) =>
        IO.println s!"  counterexample: input stack (top first) {shw din stk}: {what} differs"
      | none => IO.println "  (no concrete counterexample found)"
    return 1
  | _, _ =>
    IO.eprintln "unsupported instruction (only straight-line code: no jumps, calls, SSTORE, …)"
    return 2

def loadJson (path : String) : IO Lean.Json := do
  match Lean.Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw (IO.userError s!"{path}: {e}")

def showBlock (b : Block) : String := " ".intercalate (b.map Instr.show)
def showX (b : XBlock) : String := " ".intercalate (b.map XInstr.show)

/-- Validate gasol's optimised asm against the original, block by block. -/
def gasolCmp (f : Fork) (orig opt : String) (verbose : Bool) : IO Unit := do
  let jo ← loadJson orig
  let jg ← loadJson opt
  let co := contractCodes jo
  let cg := contractCodes jg
  let mut nSame := 0; let mut nOk := 0; let mut nRej := 0; let mut nBug := 0
  let mut nMixed := 0; let mut nMis := 0; let mut gasBefore := 0; let mut gasAfter := 0
  let mut gOrig := 0; let mut gGasol := 0; let mut gOurs := 0
  let mut oursBetter := 0; let mut gasolBetter := 0
  let mut nEff := 0; let mut nEffSame := 0; let mut nEffOk := 0; let mut nEffBad := 0
  let mut nEffUnval := 0
  for (name, codesO) in co do
    let some codesG := cg.lookup name | continue
    for (ao, ag) in codesO.zip codesG do
      let bo := splitBlocks (ao.toList.map (solcItem f))
      let bg := splitBlocks (ag.toList.map (solcItem f))
      if bo.length != bg.length then
        nMis := nMis + 1
        if verbose then IO.println s!"[mismatch] {name}: {bo.length} vs {bg.length} blocks"
        continue
      for (xo, xg) in bo.zip bg do
        match stackOnly (body xo), stackOnly (body xg) with
        | some b, some b' =>
          let ours := optimizeBlock f b
          let gasolOk := b == b' || check f b b'
          let cg := if gasolOk then cost f b' else cost f b
          gOrig := gOrig + cost f b; gGasol := gGasol + cg; gOurs := gOurs + cost f ours
          if cost f ours < cg then oursBetter := oursBetter + 1
          else if cg < cost f ours then
            gasolBetter := gasolBetter + 1
            if verbose then
              IO.println s!"[gasol better] {showBlock b}\n  gasol: {showBlock b'}\n  ours:  {showBlock ours}"
          if b == b' then nSame := nSame + 1
          else if check f b b' then
            nOk := nOk + 1; gasBefore := gasBefore + cost f b; gasAfter := gasAfter + cost f b'
          else
            nRej := nRej + 1
            let cex := counterexample f b b'
            if cex.isSome then nBug := nBug + 1
            IO.println s!"[{if cex.isSome then "WRONG" else "unvalidated"}] {checkReason f b b'}"
            IO.println s!"  orig:  {showBlock b}"
            IO.println s!"  gasol: {showBlock b'}"
            if let some (stk, r, r') := cex then
              IO.println s!"  input (top first): {stk.take 8}"
              IO.println s!"  orig result: {r.take 8}"
              IO.println s!"  gasol result: {r'.map (·.take 8)}"
        | _, _ =>
          match effectBlock (body xo), effectBlock (body xg) with
          | some b, some b' =>
            nEff := nEff + 1
            if b == b' then nEffSame := nEffSame + 1
            else if xcheck f b b' then nEffOk := nEffOk + 1
            else match xcounterexample f b b' with
              | some (what, stk) =>
                nEffBad := nEffBad + 1
                IO.println s!"[WRONG effect block: {what}] input top {stk}"
                IO.println s!"  orig:  {showX b}"
                IO.println s!"  gasol: {showX b'}"
              | none => nEffUnval := nEffUnval + 1
          | _, _ => nMixed := nMixed + 1
  IO.println s!"blocks: unchanged {nSame}, validated {nOk} (gas {gasBefore} -> {gasAfter}), \
    rejected {nRej} (with concrete counterexample: {nBug}), non-stack {nMixed}, \
    code-level block-count mismatches {nMis}"
  IO.println s!"effect blocks: {nEff} (unchanged {nEffSame}, validated {nEffOk}, \
    wrong {nEffBad}, effects changed and no counterexample found {nEffUnval})"
  IO.println s!"stack-only blocks gas: original {gOrig}, gasol (validated only) {gGasol}, \
    ours {gOurs}; ours better on {oursBetter}, gasol better on {gasolBetter}"

/-- Our peephole optimizer over every block of a solc asm json. -/
def statsJson (f : Fork) (path : String) : IO Unit := do
  let j ← loadJson path
  let mut before := 0; let mut after := 0; let mut sb := 0; let mut sa := 0; let mut n := 0
  for (_, codes) in contractCodes j do
    for code in codes do
      for blk in splitBlocks (code.toList.map (solcItem f)) do
        let out := optimizeItems f blk
        n := n + 1
        before := before + itemsCost f blk; after := after + itemsCost f out
        sb := sb + itemsSize blk; sa := sa + itemsSize out
  IO.println s!"{path}: {n} blocks, stack-op gas {before} -> {after}, stack-op bytes {sb} -> {sa}"

def parseFork : String → Option Fork
  | "london" => some .London | "paris" => some .Paris | "shanghai" => some .Shanghai
  | "cancun" => some .Cancun | "prague" => some .Prague | "osaka" => some .Osaka
  | _ => none

def main (args : List String) : IO UInt32 := do
  let (f, args) := match args with
    | "--fork" :: name :: rest => ((parseFork name).getD .Cancun, rest)
    | rest => (.Cancun, rest)
  match args with
  | ["gasolcmp", a, b] => gasolCmp f a b false; return 0
  | ["gasolcmp", "-v", a, b] => gasolCmp f a b true; return 0
  | "stats" :: paths => for p in paths do statsJson f p
                        return 0
  | ["optimize", path] => optimizeFile f path; return 0
  | ["verify", a, b] => verifyPair f a b
  | _ =>
    IO.eprintln "usage: evmopt [--fork F] (optimize <blocks.txt> | verify \"<original>\" \"<candidate>\" | stats <asm.json>... | gasolcmp [-v] <orig.json> <gasol.json>)"
    return 2
