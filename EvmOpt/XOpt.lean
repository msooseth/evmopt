import EvmOpt.MemTags
import EvmOpt.Search

/-! Untrusted optimisation of effect blocks; every candidate goes through `xcheck`. -/

namespace EvmOpt
open EvmSemantics EvmSemantics.EVM

def XInstr.base? : XInstr → Option Instr
  | .base i => some i
  | _ => none

def xcost (f : Fork) (b : XBlock) : Nat :=
  (b.map fun | .base i => i.cost f | .tag _ => tagCost | .mem _ => 0).sum

/-- Schedulers work on blocks where each tag is a sentinel PUSH3; any misuse of a sentinel
    (e.g. computing it instead of pushing it) is caught by `xcheck` on the real blocks. -/
def sentinel (k : Nat) : List UInt8 := [0xfe, (k / 256 % 256).toUInt8, (k % 256).toUInt8]

def toSentinel (b : XBlock) : XBlock :=
  b.map fun | .tag k => .base (.push (sentinel k)) | x => x

def fromSentinel (b : XBlock) : XBlock :=
  b.map fun
    | .base (.push [0xfe, h, l]) => .tag (h.toNat * 256 + l.toNat)
    | x => x
def xsize (b : XBlock) : Nat := (xencode b).length
def xscore (f : Fork) (b : XBlock) : Nat := xcost f b + 3 * xsize b

/-- Split at effects: stack-only segments and the effects between them. -/
def segments : XBlock → List (Sum Block MemOp)
  | [] => []
  | .mem m :: b => .inr m :: segments b
  | .tag _ :: b => segments b
  | .base i :: b =>
    match segments b with
    | .inl seg :: rest => .inl (i :: seg) :: rest
    | rest => .inl [i] :: rest

/-- Optimise each stack-only segment on its own (its interface stays fixed). -/
def segOpt (f : Fork) (b : XBlock) : XBlock :=
  fromSentinel <| (segments (toSentinel b)).flatMap fun
    | .inl seg => (optimizeBlock f seg).map .base
    | .inr m => [.mem m]

/-- Greedy lowering that emits the effects in their original order. -/
def xgreedyWith (pre bottom reserve : Bool) (f : Fork) (b0 : XBlock) : Option XBlock := do
  let b := toSentinel b0
  let X ← xlift f b
  let goal := X.S.ts.map norm
  let effs := (X.E.map fun e => (e.1, e.2.map norm)).toArray
  let all := goal ++ effs.toList.flatMap (·.2)
  let distinct := (all.flatMap Term.subterms).eraseDups
  let d0 : Demand := all.foldl (fun d t => d.insert t (d.get t + 1)) {}
  let demand := (distinct.filter fun t => t.instr.isSome).foldl
    (fun d t => t.args.foldl (fun d a => d.insert a (d.get a + 1)) d) d0
  let init := (List.range X.S.d).map Term.var
  let (init, pre0) := if pre then preclean init demand else (init, [])
  -- emit effects `k .. upto-1` in order
  let flush := fun (upto : Nat) (st : List Term × List XInstr × Demand × Nat) => do
    let mut (c, pr, dd, k) := st
    while k < upto do
      let (m, args) := effs[k]!
      let (c', p', dd', _) ← args.reverse.foldlM (fun (c, pr, dd, first) a => do
        let (c', p', dd') ← emit f a c dd (if first then .first else .later)
        return (c', pr ++ p', dd', false)) (c, [], dd, true)
      c := (if m.pushes then [Term.eff k] else []) ++ c'.drop m.arity
      pr := pr ++ p'.map XInstr.base ++ [XInstr.mem m]
      dd := dd'
      k := k + 1
    return (c, pr, dd, k)
  -- goal deepest first; an effect is emitted just before the first term that needs it
  let keep := if bottom then commonBottom init goal else 0
  let st ← (goal.take (goal.length - keep)).reverse.foldlM (fun st t =>
      if !bottom && st.1.contains t then some st else do
      let (c, pr, dd, k) ← flush t.effBound st
      let (c', p', dd') ← emit f t c dd (if reserve then .top else .topKeep)
      return (c', pr ++ p'.map XInstr.base, dd', k)) (init, [], demand, 0)
  let (cur, prog, _, _) ← flush effs.size st
  let fix ← shuffle cur goal
  return fromSentinel (pre0.map XInstr.base ++ prog ++ fix.map XInstr.base)

def xgreedy (f : Fork) (b : XBlock) : Option XBlock :=
  [false, true].flatMap (fun p => [false, true].flatMap fun q => [(p, q, false), (p, q, true)])
  |>.foldl (fun best (pre, bot, res) =>
    match (xgreedyWith pre bot res f b).filter (xcheck f b ·), best with
    | some c, some x => if xscore f c < xscore f x then some c else some x
    | some c, none => some c
    | none, x => x) none

/-- Cheapest-first search for effect blocks: effects only in their original order and only on
    arguments equal (after normalisation) to the original's. -/
def xsearch (f : Fork) (b0 : XBlock) (maxNodes : Nat := 5000) : Option XBlock := Id.run do
  let b := toSentinel b0
  let some X := xlift f b | return none
  let target := X.S.ts.map norm
  let effs := (normE X.E).toArray
  let all := target ++ effs.toList.flatMap (·.2)
  let subs : Std.HashMap Term Unit := (all.flatMap Term.subterms).foldl (fun m t => m.insert t ()) {}
  let consts := (all.flatMap Term.subterms).filterMap fun | .const v => some v | _ => none
  let ops := ((all.flatMap Term.subterms).filterMap Term.op?).eraseDups
  let envs := ((all.flatMap Term.subterms).filterMap fun
    | .env0 e | .env1 e _ => some e | _ => none).eraseDups
  let pushes := (consts.eraseDups.map (pushOf f)).filter (·.static f)
  let budget := xcost f b
  let sizeBudget := xsize b
  let moves (T : XSState) : List XInstr :=
    let avail := T.S.ts.length + (X.S.d - T.S.d)
    (((List.range 16).filterMap fun n =>
      if h : n < 16 then if n < avail then some (Instr.dup ⟨n, h⟩) else none else none) ++
    ((List.range 16).filterMap fun n =>
      if h : n < 16 then if n + 1 < avail then some (Instr.swap ⟨n, h⟩) else none else none) ++
    (if 0 < avail then [Instr.pop] else []) ++ pushes ++
    (ops.filterMap fun o => if o.arity ≤ avail then some (Instr.op o) else none) ++
    (envs.filterMap fun e => if e.arity ≤ avail then some (Instr.env e) else none)).map .base ++
    (match effs[T.E.length]? with
     | some (m, _) => if m.arity ≤ avail then [.mem m] else []
     | none => [])
  let useful (x : XInstr) (T : XSState) : Bool :=
    match x with
    | .base (.op _) | .base (.env _) => match T.S.ts.head? with
      | some t => subs.contains t
      | none => false
    | .mem _ => (T.E.getLast?.map fun e => (e.1, e.2.map norm)) == effs[T.E.length - 1]?
    | _ => true
  let mut frontier : Std.TreeMap Nat (List (XSState × List XInstr × Nat)) :=
    Std.TreeMap.empty.insert 0 [(XSState.init, [], 0)]
  let mut seen : Std.HashMap (List Term × Nat × Nat) Nat := {}
  let mut nodes := 0
  while nodes < maxNodes do
    let some (g, bucket) := frontier.minEntry? | return none
    match bucket with
    | [] => frontier := frontier.erase g
    | (T, prog, sz) :: rest =>
      frontier := frontier.insert g rest
      nodes := nodes + 1
      if T.E.length == effs.size && reaches X.S T.S then
        let cand := prog.reverse
        return if xcost f cand < budget then some (fromSentinel cand) else none
      if prog.length ≥ b.length + 2 then continue
      for x in moves T do
        let g' := g + (match x with | .base i => i.cost f | _ => 0)
        let sz' := sz + x.size
        if g' ≥ budget || sz' > sizeBudget + (budget - g') / 3 then continue
        let some T1 := xsstep f x T | continue
        let T' := { T1 with S := normState T1.S }
        if T'.S.d > X.S.d || !useful x T' then continue
        let key := (T'.S.ts, T'.S.d, T'.E.length)
        if (seen.get? key).any (· ≤ g') then continue
        seen := seen.insert key g'
        frontier := frontier.insert g' ((T', x :: prog, sz') :: (frontier.getD g' []))
  return none

/-- Keep `c` only if `xcheck` accepts it and it scores better (gas + 3·bytes). -/
def xtry (f : Fork) (b c : XBlock) : XBlock :=
  if xcheck f b c && decide (xscore f c < xscore f b) then c else b

/-- With tags assembled by `ρ`, `b` reaches from `s0` the frame the original reached (`s1`)
    except pc, with no less gas. -/
def Good (f : Fork) (ρ : Nat → List UInt8) (s0 s1 : State) (b : XBlock) : Prop :=
  ∃ s2, xrun f (assemble ρ b) s0 = some s2 ∧
    s2 = { s1 with gasAvailable := s2.gasAvailable, pc := s2.pc } ∧
    s1.gasAvailable ≤ s2.gasAvailable

def TagsFit (ρ : Nat → List UInt8) : Prop := ∀ k, 1 ≤ (ρ k).length ∧ (ρ k).length ≤ 32

theorem good_refl {f : Fork} {ρ : Nat → List UInt8} {b : XBlock} {s0 s1 : State}
    (h : xrun f (assemble ρ b) s0 = some s1) : Good f ρ s0 s1 b := ⟨s1, h, rfl, Nat.le_refl _⟩

theorem xtry_good {f : Fork} {ρ : Nat → List UInt8} {s0 s1 : State} {b : XBlock} (hρ : TagsFit ρ)
    (hl : s0.stack.length ≤ 1024) (hg : Good f ρ s0 s1 b) (c : XBlock) :
    Good f ρ s0 s1 (xtry f b c) := by
  obtain ⟨s2, h2, e2, g2⟩ := hg
  unfold xtry
  split
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    obtain ⟨s3, h3, e3, g3⟩ := xcheck_sound_asm ρ hρ hc.1 hl h2
    exact ⟨s3, h3, by rw [e3, e2], by omega⟩
  · exact ⟨s2, h2, e2, g2⟩

def tryOpt (f : Fork) (o : Option XBlock) (b : XBlock) : XBlock :=
  match o with
  | some c => xtry f b c
  | none => b

theorem tryOpt_good {f : Fork} {ρ : Nat → List UInt8} {s0 s1 : State} {b : XBlock}
    (hρ : TagsFit ρ) (hl : s0.stack.length ≤ 1024) (hg : Good f ρ s0 s1 b) (o : Option XBlock) :
    Good f ρ s0 s1 (tryOpt f o b) := by
  unfold tryOpt; split
  · exact xtry_good hρ hl hg _
  · exact hg

/-- Exact search on sliding windows of a long block; each improvement is validated on the
    whole block by `xcheck`. -/
def windowOpt (f : Fork) (b : XBlock) (w : Nat := 8) (step : Nat := 4) : XBlock := Id.run do
  let mut cur := b
  let mut i := 0
  while i + 2 < cur.length do
    let win := (cur.drop i).take w
    match xsearch f win 1500 with
    | some c =>
      let cand := cur.take i ++ c ++ cur.drop (i + win.length)
      let next := xtry f cur cand
      if next != cur then cur := next
    | none => pure ()
    i := i + step
  return cur

def searchStage (f : Fork) (b b2 : XBlock) : XBlock :=
  if b.any (fun x => x matches .mem _ || x matches .tag _) && b2.length ≤ 24 then
    tryOpt f (xsearch f b2) b2
  else b2

def windowStage (f : Fork) (b3 : XBlock) : XBlock :=
  if b3.length > 12 then xtry f b3 (windowOpt f b3) else b3

def optimizeX (f : Fork) (b : XBlock) : XBlock :=
  let b1 := xtry f b (segOpt f b)
  let b2 := tryOpt f (xgreedy f b1) b1
  windowStage f (searchStage f b b2)

theorem searchStage_good {f : Fork} {ρ : Nat → List UInt8} {s0 s1 : State} {b b2 : XBlock}
    (hρ : TagsFit ρ) (hl : s0.stack.length ≤ 1024) (hg : Good f ρ s0 s1 b2) :
    Good f ρ s0 s1 (searchStage f b b2) := by
  unfold searchStage; split
  · exact tryOpt_good hρ hl hg _
  · exact hg

theorem windowStage_good {f : Fork} {ρ : Nat → List UInt8} {s0 s1 : State} {b3 : XBlock}
    (hρ : TagsFit ρ) (hl : s0.stack.length ≤ 1024) (hg : Good f ρ s0 s1 b3) :
    Good f ρ s0 s1 (windowStage f b3) := by
  unfold windowStage; split
  · exact xtry_good hρ hl hg _
  · exact hg

/-- **Optimiser soundness.** For every tag assignment, if the assembled original runs from
    `s0` to `s1`, the assembled optimised block reaches `s1` except pc, with no less gas. -/
theorem optimizeX_sound {f : Fork} {ρ : Nat → List UInt8} {b : XBlock} {s0 s1 : State}
    (hρ : TagsFit ρ) (hl : s0.stack.length ≤ 1024) (h : xrun f (assemble ρ b) s0 = some s1) :
    Good f ρ s0 s1 (optimizeX f b) := by
  have h1 := xtry_good hρ hl (good_refl h) (segOpt f b)
  have h2 := tryOpt_good hρ hl h1 (xgreedy f (xtry f b (segOpt f b)))
  exact windowStage_good hρ hl (searchStage_good hρ hl h2)

/-- Why `xcheck` rejects, for reports. -/
def xcheckReason (f : Fork) (b b' : XBlock) : String :=
  match xlift f b, xlift f b' with
  | none, _ => "original contains an unsupported instruction"
  | _, none => "candidate contains an unsupported instruction"
  | some X, some X' =>
    if normE X.E != normE X'.E then
      if X.E.map (·.1) == X'.E.map (·.1) then "memory/storage operations get different arguments (e.g. reordered stores; not supported yet)"
      else "candidate drops, adds or reorders memory/storage operations (not supported yet)"
    else if X'.S.d > X.S.d then "candidate reads deeper into the stack than the original"
    else if X.S.slack + ((X.S.d : Int) - X'.S.d) > X'.S.slack then "candidate needs more stack space than the original (could overflow the 1024 limit)"
    else if X'.sc > X.sc then "candidate costs more gas"
    else if xcheck f b b' then "ok"
    else "results differ, or could not be proven equal"

end EvmOpt
