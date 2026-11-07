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

/-- Peephole, then search on the result; the search output must pass `check`. -/
def optimizeBlock (f : Fork) (b : Block) : Block :=
  let p := peephole f b
  match search f p with
  | some c => if check f p c then c else p
  | none => p

theorem optimizeBlock_sound (f : Fork) (σ : State) (b : Block) {stk r : List UInt256}
    (hl : stk.length ≤ 1024) (h : run f σ b stk = some r) :
    run f σ (optimizeBlock f b) stk = some r ∧ cost f (optimizeBlock f b) ≤ cost f b := by
  obtain ⟨h1, h2⟩ := peephole_sound f σ b hl h
  unfold optimizeBlock
  dsimp only
  split
  · split
    · next hc => obtain ⟨h3, h4⟩ := check_sound hc hl h1; exact ⟨h3, by omega⟩
    · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

end EvmOpt
