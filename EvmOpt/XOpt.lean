import EvmOpt.MemLift
import EvmOpt.Search

/-! Untrusted optimisation of effect blocks; every candidate goes through `xcheck`. -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

def XInstr.base? : XInstr → Option Instr
  | .base i => some i
  | .mem _ => none

def xcost (f : Fork) (b : XBlock) : Nat := cost f (b.filterMap XInstr.base?)
def xsize (b : XBlock) : Nat := (xencode b).length
def xscore (f : Fork) (b : XBlock) : Nat := xcost f b + 3 * xsize b

/-- Split at effects: stack-only segments and the effects between them. -/
def segments : XBlock → List (Sum Block MemOp)
  | [] => []
  | .mem m :: b => .inr m :: segments b
  | .base i :: b =>
    match segments b with
    | .inl seg :: rest => .inl (i :: seg) :: rest
    | rest => .inl [i] :: rest

/-- Optimise each stack-only segment on its own (its interface stays fixed). -/
def segOpt (f : Fork) (b : XBlock) : XBlock :=
  (segments b).flatMap fun
    | .inl seg => (optimizeBlock f seg).map .base
    | .inr m => [.mem m]

/-- Greedy lowering that emits the effects in their original order. -/
def xgreedyWith (pre : Bool) (f : Fork) (b : XBlock) : Option XBlock := do
  let X ← xlift f b
  let goal := X.S.ts.map norm
  let effs := X.E.map fun e => (e.1, e.2.map norm)
  let all := goal ++ effs.flatMap (·.2)
  let distinct := (all.flatMap Term.subterms).eraseDups
  let d0 : Demand := all.foldl (fun d t => d.insert t (d.get t + 1)) {}
  let demand := (distinct.filter fun t => t.instr.isSome).foldl
    (fun d t => t.args.foldl (fun d a => d.insert a (d.get a + 1)) d) d0
  let init := (List.range X.S.d).map Term.var
  let (init, pre0) := if pre then preclean init demand else (init, [])
  let (cur, prog, dem, _) ← effs.foldlM (fun (c, pr, dd, k) (m, args) => do
    let (c', p', dd', _) ← args.reverse.foldlM (fun (c, pr, dd, first) a => do
      let (c', p', dd') ← emit f a c dd (if first then .first else .later)
      return (c', pr ++ p', dd', false)) (c, [], dd, true)
    let c'' := (if m.pushes then [Term.eff k] else []) ++ c'.drop m.arity
    return (c'', pr ++ p'.map XInstr.base ++ [XInstr.mem m], dd', k + 1)) (init, [], demand, 0)
  let (cur, prog2, _) ← goal.reverse.foldlM (fun (c, pr, d) t =>
    if c.contains t then some (c, pr, d) else do
      let (c', p', d') ← emit f t c d
      return (c', pr ++ p', d')) (cur, [], dem)
  let fix ← shuffle cur goal
  return pre0.map XInstr.base ++ prog ++ (prog2 ++ fix).map XInstr.base

def xgreedy (f : Fork) (b : XBlock) : Option XBlock :=
  let c1 := (xgreedyWith false f b).filter fun c => xcheck f b c
  let c2 := (xgreedyWith true f b).filter fun c => xcheck f b c
  match c1, c2 with
  | some x, some y => if xscore f y < xscore f x then some y else some x
  | some x, none => some x
  | none, y => y

/-- Keep `c` only if `xcheck` accepts it and it scores better (gas + 3·bytes). -/
def xtry (f : Fork) (b c : XBlock) : XBlock :=
  if xcheck f b c && decide (xscore f c < xscore f b) then c else b

theorem xtry_sound {f : Fork} {b c : XBlock} {s0 s1 : State} (hl : s0.stack.length ≤ 1024)
    (h : xrun f b s0 = some s1) :
    ∃ s2, xrun f (xtry f b c) s0 = some s2 ∧
      s2 = { s1 with gasAvailable := s2.gasAvailable, pc := s2.pc } ∧
      s1.gasAvailable ≤ s2.gasAvailable := by
  unfold xtry
  split
  · next hc => simp only [Bool.and_eq_true] at hc; exact xcheck_sound hc.1 hl h
  · exact ⟨s1, h, rfl, Nat.le_refl _⟩

def optimizeX (f : Fork) (b : XBlock) : XBlock :=
  let b1 := xtry f b (segOpt f b)
  match xgreedy f b1 with
  | some c => xtry f b1 c
  | none => b1

theorem optimizeX_sound {f : Fork} {b : XBlock} {s0 s1 : State} (hl : s0.stack.length ≤ 1024)
    (h : xrun f b s0 = some s1) :
    ∃ s2, xrun f (optimizeX f b) s0 = some s2 ∧
      s2 = { s1 with gasAvailable := s2.gasAvailable, pc := s2.pc } ∧
      s1.gasAvailable ≤ s2.gasAvailable := by
  obtain ⟨s2, h2, e2, g2⟩ := xtry_sound (c := segOpt f b) hl h
  unfold optimizeX
  dsimp only
  split
  · next c _ =>
    obtain ⟨s3, h3, e3, g3⟩ := xtry_sound (c := c) hl h2
    refine ⟨s3, h3, ?_, by omega⟩
    rw [e3, e2]
  · exact ⟨s2, h2, e2, g2⟩

end EvmOpt
