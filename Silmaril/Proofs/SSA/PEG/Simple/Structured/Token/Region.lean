module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Body
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Loop
public import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Simple.Proofs (get_map get_select ports_get)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars outs before inside all : List (Ty Data)}
variable {m : Interpretation.{u,v,w} P}
variable {env : Tuple m.Value params} {read : Reads (model m) all}
variable {active : List (Fin all.length)} {fixed : Index all.length}

theorem phiViewRead {ty : Ty Data} (flag : Port before .bool)
    (yes no : Tuple (Port before) outs)
    (v : View (model m) env read active (.straight (phiNodes flag yes no).code))
    (i : Index all.length) (slot : Port outs ty) :
    let joined := phiNodes (P := Opcode P) (params := params) flag yes no
    read (v.embed (joined.refs.get slot)) i =
      (read (v.embed (joined.code.lift flag)) i).elim none (fun b =>
        if b.down then read (v.embed (joined.code.lift (yes.get slot))) i
        else read (v.embed (joined.code.lift (no.get slot))) i) := by
  dsimp only
  rw [v.straightRead, phiRead]
  simp only [View.seed, get_map, ports_get]
  cases read (v.embed ((phiNodes flag yes no).code.lift flag)) i with
  | none => rfl
  | some b =>
    obtain ⟨b⟩ := b
    cases b <;> rfl

abbrev pack (m : Interpretation.{u,v,w} P) (store : Tuple m.Value vars) :
    Tuple (model m).Value (.bool :: vars) := .cons ⟨true⟩ store

theorem sliceExact (body : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (v : View (model m) env read active (.straight (body.lower ctx).code))
    (store : Tuple m.Value vars)
    (entry : RealizesOn read (fun r => v.embed ((body.lower ctx).code.lift r))
      ctx (pack m store) active fixed) :
    match body.source.runLoopFree m store with
    | none => ∀ j, Agrees active fixed j → read (v.embed ((body.lower ctx).refs.get .head)) j = none
    | some next => RealizesOn read v.embed (body.lower ctx).refs (pack m next) active fixed := by
  have exactAt j agree := bodyExact m env body ctx (v.seed j) ⟨true⟩ store (v.seedRealizes (entry j agree))
  cases ran : body.source.runLoopFree m store with
  | none =>
    intro j agree
    exact (v.straightRead j _).trans (by simpa only [ran] using exactAt j agree)
  | some next =>
    intro j agree ty slot
    have realizes : Realizes (model m) ((body.lower ctx).code.eval (model m) env (v.seed j))
        (body.lower ctx).refs (pack m next) := by simpa only [ran] using exactAt j agree
    exact (v.straightRead j _).trans (realizes ty slot)

theorem sliceBottom (body : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (v : View (model m) env read active (.straight (body.lower ctx).code)) (i : Index all.length)
    (entry : read (v.embed ((body.lower ctx).code.lift (ctx.get .head))) i = none) :
    read (v.embed ((body.lower ctx).refs.get .head)) i = none := by
  apply (v.straightRead i _).trans
  apply bodyBottom
  simpa only [View.seed, get_map, ports_get] using entry

private theorem guardFromFlag (test : Option (ULift.{w} Bool)) {flag : Bool}
    (h : test.map (fun b => !b.down) = some (!flag)) : test = some ⟨flag⟩ := by
  cases test with
  | none => cases h
  | some actual =>
    obtain ⟨actual⟩ := actual
    cases actual <;> cases flag <;> simp_all

variable {init : Tuple (Port before) (.bool :: vars)}
variable {code : Code (Opcode P) params ((.bool :: vars) ++ before) inside}
variable {cond : Port inside .bool} {next : Tuple (Port inside) (.bool :: vars)}
variable {neg : Opcode P [.bool] .bool}
variable (view : View (model m) env read active (.loop init code cond next neg))

/-- Local simulation at one iteration. A defined emitted feedback token
justifies the entire source body. The additional observation belongs to
that same iteration, even when its computation contains a child pass. -/
structure LoopFacts (test : Expr P vars .bool) (body : Stmt P true vars vars)
    (reached : Index all.length → Prop) : Prop where
  guardAt : ∀ {i k store}, AtIteration view i k (pack m store) →
    ∀ j, Agrees active i j →
      read (view.inner.embed cond) (j.set view.key k) = test.eval m store
  bodyReturns : ∀ {i k store final}, AtIteration view i k (pack m store) →
    Exec m body store (some final) →
    RealizesOn read view.inner.embed next (pack m final) (view.key :: active) (i.set view.key k)
  bodyOfToken : ∀ {i k store}, AtIteration view i k (pack m store) →
    (read (view.inner.embed (next.get .head)) (i.set view.key k)).isSome →
    ∃ final, Exec m body store (some final) ∧
      RealizesOn read view.inner.embed next (pack m final) (view.key :: active) (i.set view.key k) ∧
      reached (i.set view.key k)

variable {test : Expr P vars .bool} {body : Stmt P true vars vars}
variable {reached : Index all.length → Prop}
variable (facts : LoopFacts view test body reached)
variable (negSem : ∀ b : Bool, (model m).run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)

include facts negSem in
theorem LoopFacts.ofTrace {store final : Tuple m.Value vars} {count : Nat}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init code cond next neg).lift r))
      init (pack m store) active fixed)
    (trace : WhileTrace m test body count store final) :
    RealizesOn read view.embed ((ports (.bool :: vars)).map fun _ p => portLeft p)
      (pack m final) active fixed ∧
    (∀ j, Agrees active fixed j →
      read (view.embed (passRef (.bool :: vars))) j = some ⟨count⟩) := by
  have exit := traceExit view (pack m) negSem fixed
    (fun aligned eq j agrees => (facts.guardAt aligned j agrees).trans eq)
    facts.bodyReturns trace 0 (atEntry view entry)
  refine ⟨?_, fun j agree => passValue view exit j agree⟩
  intro j agree ty p
  rw [get_map, ports_get]
  exact evalValue view exit j agree p

include facts negSem in
private theorem traceFromCompletion (start count : Nat) {store : Tuple m.Value vars}
    (aligned : AtIteration view fixed start (pack m store))
    (stop : flags view fixed (start + count) = some true)
    (prior : ∀ j < count, flags view fixed (start + j) = some false)
    (defined : ∀ j ≤ count, (samples view fixed .head (start + j)).isSome) :
    ∃ final, WhileTrace m test body count store final ∧
      ∀ j < count, reached (fixed.set view.key (start + j)) := by
  have flag {k store} (atK : AtIteration view fixed k (pack m store)) :
      flags view fixed k = (test.eval m store).map (fun b => !b.down) := by
    unfold flags
    rw [exitTestExact view negSem, facts.guardAt atK fixed (agrees_self active fixed)]
    cases test.eval m store <;> rfl
  induction count generalizing start store with
  | zero =>
    rw [Nat.add_zero, flag aligned] at stop
    exact ⟨store, .stop (guardFromFlag _ (flag := false) stop), fun j lt => by omega⟩
  | succ count ih =>
    have continues := prior 0 (Nat.zero_lt_succ _)
    rw [Nat.add_zero, flag aligned] at continues
    have feedback := defined 1 (by omega)
    rw [samples_succ view fixed .head start] at feedback
    obtain ⟨next, run, progressed, here⟩ := facts.bodyOfToken aligned feedback
    have offset (j : Nat) : start + 1 + j = start + (j + 1) := by omega
    obtain ⟨final, rest, tail⟩ := ih (start + 1) (stepIteration view progressed)
      (by rwa [offset]) (fun j hj => by rw [offset]; exact prior (j + 1) (by omega))
      (fun j hj => by rw [offset]; exact defined (j + 1) (by omega))
    refine ⟨final, .step (guardFromFlag _ (flag := true) continues) run rest, ?_⟩
    intro j lt
    cases j with
    | zero => exact here
    | succ j => rw [← offset]; exact tail j (by omega)

include facts negSem in
theorem LoopFacts.ofCompletion {store : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init code cond next neg).lift r))
      init (pack m store) active fixed)
    (complete : (read (view.embed (portLeft .head)) fixed).isSome) :
    ∃ count final, WhileTrace m test body count store final ∧
      read (view.embed (passRef (.bool :: vars))) fixed = some ⟨count⟩ ∧
      ∀ j < count, reached (fixed.set view.key j) := by
  rw [evalEquation view fixed .head, passEquation view fixed] at complete
  cases pass : firstTrue (flags view fixed) with
  | none => simp [pass] at complete
  | some count =>
    rw [pass] at complete
    change (monotonize (samples view fixed .head) count).isSome at complete
    obtain ⟨stop, prior⟩ := (firstTrue_eq_some_iff_samples _ _).mp pass
    have available (j : Nat) (le : j ≤ count) : (samples view fixed .head j).isSome := by
      cases tok : monotonize (samples view fixed .head) count with
      | none => simp [tok] at complete
      | some b =>
        obtain ⟨last, earlier⟩ := (monotonize_eq_some_iff _ _ _).mp tok
        rcases Nat.lt_or_eq_of_le le with lt | rfl
        · exact earlier _ lt
        · simp [last]
    obtain ⟨final, trace, used⟩ := traceFromCompletion view facts negSem 0 count (atEntry view entry)
      (by simpa only [Nat.zero_add] using stop) (by simpa only [Nat.zero_add] using prior)
      (by simpa only [Nat.zero_add] using available)
    refine ⟨count, final, trace, ?_, by simpa only [Nat.zero_add] using used⟩
    rw [passEquation view fixed, pass]
    rfl

theorem guardAligned (test : Expr P vars .bool)
    (suffix : Code (Opcode P) params (loopTest test params before).nodes inside)
    (v : View (model m) env read active (.loop init
      (.seq (.straight (loopTest test params before).code) suffix)
      (suffix.lift ((loopTest test params before).refs.get .head)) next neg))
    {k : Nat} {store : Tuple m.Value vars} (aligned : AtIteration v fixed k (pack m store))
    (j : Index all.length) (agree : Agrees active fixed j) :
    read (v.inner.embed (suffix.lift ((loopTest test params before).refs.get .head)))
        (j.set v.key k) = test.eval m store := by
  let testCode := loopTest test params before
  let point := j.set v.key k
  have atPoint := aligned point (sampleAgrees v agree k)
  have data : RealizesAt read (fun r => v.inner.left.embed (testCode.code.lift r))
      (tail (loopSlots vars before)) store point := fun ty slot => atPoint ty (.tail slot)
  exact (v.inner.left.straightRead point (testCode.refs.get .head)).trans
    (exprExact m env test (tail (loopSlots vars before)) (v.inner.left.seed point) store
      (v.inner.left.seedRealizes data))

/-- The code following a compiled loop guard sees the same carried tuple
at every index agreeing with this iteration and its enclosing coordinates. -/
theorem loopScopeAligned (test : Expr P vars .bool)
    (suffix : Code (Opcode P) params (loopTest test params before).nodes inside)
    (v : View (model m) env read active (.loop init
      (.seq (.straight (loopTest test params before).code) suffix)
      (suffix.lift ((loopTest test params before).refs.get .head)) next neg))
    {k : Nat} {store : Tuple m.Value vars} (aligned : AtIteration v fixed k (pack m store)) :
    RealizesOn read (fun r => v.inner.right.embed (suffix.lift r))
      ((loopTest test params before).code.liftRefs (loopSlots vars before))
      (pack m store) (v.key :: active) (fixed.set v.key k) := by
  intro j agree ty slot
  change read (v.inner.embed (suffix.lift
    (((loopTest test params before).code.liftRefs (loopSlots vars before)).get slot))) j =
    some ((pack m store).get slot)
  rw [show ((loopTest test params before).code.liftRefs (loopSlots vars before)).get slot =
      (loopTest test params before).code.lift (portLeft slot) by
    simp only [Simple.Code.liftRefs, loopSlots, get_map, ports_get]]
  simpa only [get_map, ports_get, Code.lift] using aligned j agree ty slot

theorem loopFreeFacts (guard : Expr P vars .bool) (body : Body P vars vars)
    (neg : P [.bool] .bool)
    (v : View (model m) env read active (loop guard body neg init).code) :
    LoopFacts v guard body.source.enableWhile (fun _ => True) := by
  let test := loopTest guard params before
  let scope := loopSlots vars before
  let step := body.lower (params := params) (test.code.liftRefs scope)
  change View (model m) env read active (.loop init (.seq (.straight test.code) (.straight step.code))
    (step.code.lift (test.refs.get .head)) step.refs (.source neg)) at v
  have bodyAt {i k store} (carries : AtIteration v i k (pack m store)) :
      match body.source.runLoopFree m store with
      | none => ∀ j, Agrees (v.key :: active) (i.set v.key k) j →
          read (v.inner.embed (step.refs.get .head)) j = none
      | some next => RealizesOn read v.inner.embed step.refs (pack m next)
          (v.key :: active) (i.set v.key k) := by
    exact sliceExact body (test.code.liftRefs scope) v.inner.right store
      (loopScopeAligned guard (.straight step.code) v carries)
  refine ⟨fun aligned j agree => guardAligned guard (.straight step.code) v aligned j agree, ?_, ?_⟩
  · intro i k store final aligned ran
    have eq := (body.source.runLoopFree_enableWhile store).deterministic ran
    have found := bodyAt aligned
    rw [eq] at found
    exact found
  · intro i k store aligned complete
    have found := bodyAt aligned
    cases ran : body.source.runLoopFree m store with
    | none =>
      rw [ran] at found
      rw [found _ (sampleAgrees v (agrees_self active i) k)] at complete
      cases complete
    | some final =>
      rw [ran] at found
      exact ⟨final, ran ▸ body.source.runLoopFree_enableWhile store, found, trivial⟩

theorem entryAligned {env : Tuple m.Value vars} {read : Reads (model m) all}
    {code : Code (Opcode P) vars (entry P vars).nodes inside}
    (v : View (model m) env read active (.seq (.straight (entry P vars).code) code)) :
    RealizesOn read (fun r => v.right.embed (code.lift r)) (entry P vars).refs
      (pack m env) active fixed := by
  intro j _ ty slot
  refine (v.left.straightRead j ((entry P vars).refs.get slot)).trans ?_
  cases slot with
  | head => rfl
  | tail slot =>
    have value := Simple.Proofs.param_correct (model m) env (ports vars) .nil _ slot
    rw [get_select, ports_get] at value
    simp only [entry, Simple.Code.eval, Tuple.get, get_map]
    exact value

end Silmaril.SSA.PEG.Simple.Structured.Token.Proofs
