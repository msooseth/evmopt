import EvmOpt.Rules
import Std.Data.HashMap
import Std.Data.TreeMap

/-! Untrusted superoptimizing search: cheapest stack program reaching the block's SFS.
    Results are only used through `check`. -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

partial def Term.subterms (t : Term) : List Term :=
  t :: match t with
    | .app1 _ a => a.subterms
    | .app2 _ a b => a.subterms ++ b.subterms
    | .app3 _ a b c => a.subterms ++ b.subterms ++ c.subterms
    | .env1 _ a => a.subterms
    | _ => []

def Term.op? : Term → Option ArithOp
  | .app1 o _ | .app2 o _ _ | .app3 o _ _ _ => some o
  | _ => none

/-- Search state: symbolic stack with normalised terms. -/
def normState (S : SState) : SState := { S with ts := S.ts.map norm }

/-- `S'` already denotes the target `S` (same test as `check`, minus gas). -/
def reaches (S S' : SState) : Bool :=
  decide (S'.d ≤ S.d) && decide (S.slack + ((S.d : Int) - S'.d) ≤ S'.slack) &&
  (S.ts.map norm == (S'.ts ++ vars S'.d (S.d - S'.d)).map norm)

structure SearchCfg where
  maxNodes : Nat := 20000
  maxLen : Nat := 10

def search (f : Fork) (b : Block) (cfg : SearchCfg := {}) : Option Block := Id.run do
  let some S := lift f b | return none
  let target := S.ts.map norm
  let subs : Std.HashMap Term Unit :=
    (target.flatMap Term.subterms).foldl (fun m t => m.insert t ()) {}
  let consts := (target.flatMap Term.subterms).filterMap fun | .const v => some v | _ => none
  let ops := ((target.flatMap Term.subterms).filterMap Term.op?).eraseDups
  let envs := ((target.flatMap Term.subterms).filterMap fun
    | .env0 e | .env1 e _ => some e | _ => none).eraseDups
  let pushes := (consts.eraseDups.map (pushOf f)).filter (·.static f)
  let budget := cost f b
  let sizeBudget := blockSize b
  let moves (T : SState) : List Instr :=
    let avail := T.ts.length + (S.d - T.d)
    ((List.range 16).filterMap fun n =>
      if h : n < 16 then if n < avail then some (.dup ⟨n, h⟩) else none else none) ++
    ((List.range 16).filterMap fun n =>
      if h : n < 16 then if n + 1 < avail then some (.swap ⟨n, h⟩) else none else none) ++
    (if 0 < avail then [.pop] else []) ++ pushes ++
    (ops.filterMap fun o => if o.arity ≤ avail then some (.op o) else none) ++
    (envs.filterMap fun e => if e.arity ≤ avail then some (.env e) else none)
  let useful (i : Instr) (T : SState) : Bool :=
    match i with
    | .op _ | .env _ => match T.ts.head? with | some t => subs.contains t | none => false
    | _ => true
  -- frontier keyed by gas spent; each entry: state, reversed program, bytes
  let mut frontier : Std.TreeMap Nat (List (SState × List Instr × Nat)) :=
    Std.TreeMap.empty.insert 0 [(SState.init, [], 0)]
  let mut seen : Std.HashMap (List Term × Nat) Nat := {}
  let mut nodes := 0
  while nodes < cfg.maxNodes do
    let some (g, bucket) := frontier.minEntry? | return none
    match bucket with
    | [] => frontier := frontier.erase g
    | (T, prog, sz) :: rest =>
      frontier := frontier.insert g rest
      nodes := nodes + 1
      if reaches S T then
        let cand := prog.reverse
        return if cost f cand < budget && sizeOk f b cand then some cand else none
      if prog.length ≥ cfg.maxLen then continue
      for i in moves T do
        let g' := g + i.cost f
        let sz' := sz + i.size
        if g' ≥ budget || sz' > sizeBudget + (budget - g') / 3 then continue
        let T' := normState (sstep i T)
        if T'.d > S.d || !useful i T' then continue
        let key := (T'.ts, T'.d)
        if (seen.get? key).any (· ≤ g') then continue
        seen := seen.insert key g'
        frontier := frontier.insert g' ((T', i :: prog, sz') :: (frontier.getD g' []))
  return none

def Term.args : Term → List Term
  | .app1 _ a | .env1 _ a => [a]
  | .app2 _ a b => [a, b]
  | .app3 _ a b c => [a, b, c]
  | _ => []

def Term.instr : Term → Option Instr
  | .app1 o _ | .app2 o _ _ | .app3 o _ _ _ => some (.op o)
  | .env0 e | .env1 e _ => some (.env e)
  | _ => none

def countIn (t : Term) (l : List Term) : Nat := l.countP (· == t)

def dupAt (p : Nat) : Option Instr := if h : p < 16 then some (.dup ⟨p, h⟩) else none
def swapAt (p : Nat) : Option Instr :=
  if h : 1 ≤ p ∧ p ≤ 16 then some (.swap ⟨p - 1, by omega⟩) else none

def score (f : Fork) (b : Block) : Nat := cost f b + 3 * blockSize b

/-- Cheapest way (gas + 3·bytes) to materialise constant `v`; solc uses the same tricks. -/
def constRecipe (f : Fork) (v : UInt256) : Block := Id.run do
  let n := v.toNat
  let p1 (k : Nat) : Instr := pushOf f (UInt256.ofNat k)
  let mut cands : List Block := [[pushOf f v]]
  if n = UInt256.size - 1 then cands := [pushOf f (UInt256.ofNat 0), .op .NOT] :: cands
  for k in [8:256:8] do
    if n = 2 ^ k - 1 then
      cands := [p1 1, .dup ⟨0, by decide⟩, p1 k, .op .SHL, .op .SUB] :: cands
  for s in [8:256:8] do
    if n % 2 ^ s = 0 && 0 < n then
      cands := [p1 (n / 2 ^ s), p1 s, .op .SHL] :: cands
  return cands.foldl (fun best c => if score f c < score f best then c else best) [pushOf f v]

/-- Remaining uses of each term (goal occurrences + uses as an operand). -/
abbrev Demand := Std.HashMap Term Nat

def Demand.get (d : Demand) (t : Term) : Nat := d.getD t 0
def Demand.dec (d : Demand) (t : Term) : Demand := d.insert t (d.get t - 1)

/-- Put `t` on top of `cur` (top first). Uses an existing copy in place when it is on top
    and has no other remaining use; otherwise DUPs it; otherwise computes it. -/
partial def emit (f : Fork) (t : Term) (cur : List Term) (d : Demand) (canSwap : Bool := false) :
    Option (List Term × List Instr × Demand) :=
  let d := d.dec t
  let lastUse := d.get t == 0 && countIn t cur == 1
  match cur.idxOf? t with
  | some 0 =>
    if lastUse then some (cur, [], d)
    else some (t :: cur, [.dup ⟨0, by decide⟩], d)
  | some p =>
    if lastUse && canSwap then
      (swapAt p).map fun i => ((cur.exchange 0 p).getD cur, [i], d)
    else (dupAt p).map fun i => (t :: cur, [i], d)
  | none =>
    -- keep a copy below when more uses remain (CSE)
    let keep := fun (c : List Term) (pr : List Instr) (dd : Demand) =>
      if dd.get t > 0 then (t :: c, pr ++ [.dup ⟨0, by decide⟩], dd) else (c, pr, dd)
    match t with
    | .const v =>
      let r := constRecipe f v
      if cost f r > 3 then some (keep (t :: cur) r d) else some (t :: cur, r, d)
    | .var _ => none
    | _ => do
      let i ← t.instr
      let (cur', prog, d', _) ← t.args.reverse.foldlM (fun (c, pr, dd, first) a => do
        let (c', p', dd') ← emit f a c dd first
        return (c', pr ++ p', dd', false)) (cur, [], d, true)
      return keep (t :: cur'.drop t.args.length) (prog ++ [i]) d'

/-- Rearrange `cur` into exactly `goal` (both top first, over the same untouched rest). -/
partial def shuffle (cur goal : List Term) (fuel : Nat := 200) : Option (List Instr) :=
  if cur == goal then some [] else
  if fuel = 0 then none else
  -- a missing copy: DUP it
  match goal.find? (fun t => countIn t cur < countIn t goal) with
  | some t => do
    let p ← cur.idxOf? t
    let i ← dupAt p
    let rest ← shuffle (t :: cur) goal (fuel - 1)
    return i :: rest
  | none =>
  -- a surplus copy: bring it up and POP it
  match cur.findIdx? (fun t => countIn t cur > countIn t goal) with
  | some 0 => do let rest ← shuffle cur.tail goal (fuel - 1); return .pop :: rest
  | some p => do
    let i ← swapAt p
    let cur' := ((cur.exchange 0 p).getD cur)
    let rest ← shuffle cur' goal (fuel - 1)
    return i :: rest
  | none =>
  -- same multiset and length: cycle-sort with SWAPs from the top
  let wrong := fun q => cur[q]? != goal[q]?
  let top := cur.head?
  let dest := (List.range cur.length).find? fun q => 0 < q && goal[q]? == top && wrong q
  let q := match dest with
    | some q => some q
    | none => (List.range cur.length).find? fun q => 0 < q && wrong q
  match q with
  | some q => do
    let i ← swapAt q
    let rest ← shuffle ((cur.exchange 0 q).getD cur) goal (fuel - 1)
    return i :: rest
  | none => none

/-- Greedy lowering of the block's normalised SFS. -/
def greedy (f : Fork) (b : Block) : Option Block := do
  let S ← lift f b
  let goal := S.ts.map norm
  let init := (List.range S.d).map Term.var
  let distinct := (goal.flatMap Term.subterms).eraseDups
  let d0 : Demand := goal.foldl (fun d t => d.insert t (d.get t + 1)) {}
  let demand := (distinct.filter fun t => t.instr.isSome).foldl
    (fun d t => t.args.foldl (fun d a => d.insert a (d.get a + 1)) d) d0
  -- goal terms deepest first, so the shuffle mostly has to drop garbage
  let (cur, prog, _) ← goal.reverse.foldlM (fun (c, pr, d) t =>
    if c.contains t then some (c, pr, d) else do
      let (c', p', d') ← emit f t c d
      return (c', pr ++ p', d')) (init, [], demand)
  let fix ← shuffle cur goal
  return prog ++ fix

/-- DUP of an item known to be 0 becomes PUSH0 (2 gas instead of 3). -/
def dupZero (f : Fork) (b : Block) : Block := Id.run do
  if !push0Ok f then return b
  let mut S := SState.init
  let mut out : Array Instr := #[]
  for i in b do
    let i' := match i with
      | .dup n =>
        match (ensure i.need S).ts[n.val]? with
        | some t => if norm t == .const ⟨0⟩ || norm t == .const (UInt256.ofNat 0) then .push [] else i
        | none => i
      | _ => i
    out := out.push i'
    S := normState (sstep i S)
  return out.toList

/-- Keep candidate `c` for `b` only if `check` accepts it and it is an improvement under
    the size policy. -/
def tryCand (f : Fork) (b c : Block) : Block :=
  if check f b c && sizeOk f b c && decide (score f c < score f b) then c else b

theorem tryCand_sound (f : Fork) (σ : State) (b c : Block) {stk r : List UInt256}
    (hl : stk.length ≤ 1024) (h : run f σ b stk = some r) :
    run f σ (tryCand f b c) stk = some r ∧ cost f (tryCand f b c) ≤ cost f b := by
  unfold tryCand
  split
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    exact check_sound hc.1.1 hl h
  · exact ⟨h, Nat.le_refl _⟩

def cheaper (f : Fork) (a b : Option Block) : Option Block :=
  match a, b with
  | some x, some y => if score f y < score f x then some y else some x
  | some x, none => some x
  | none, y => y

/-- Peephole, DUP-of-zero, then the cheaper of search and greedy; every step after the
    peephole is checked. -/
def optimizeBlock (f : Fork) (b : Block) : Block :=
  let p := tryCand f (peephole f b) (dupZero f (peephole f b))
  let g := (greedy f p).filter fun c => check f p c
  match cheaper f (search f p) g with
  | some c => tryCand f p c
  | none => p

theorem optimizeBlock_sound (f : Fork) (σ : State) (b : Block) {stk r : List UInt256}
    (hl : stk.length ≤ 1024) (h : run f σ b stk = some r) :
    run f σ (optimizeBlock f b) stk = some r ∧ cost f (optimizeBlock f b) ≤ cost f b := by
  obtain ⟨h1, h2⟩ := peephole_sound f σ b hl h
  obtain ⟨h3, h4⟩ := tryCand_sound f σ _ (dupZero f (peephole f b)) hl h1
  unfold optimizeBlock
  dsimp only
  split
  · next c _ =>
    obtain ⟨h5, h6⟩ := tryCand_sound f σ _ c hl h3
    exact ⟨h5, by omega⟩
  · exact ⟨h3, by omega⟩

end EvmOpt
