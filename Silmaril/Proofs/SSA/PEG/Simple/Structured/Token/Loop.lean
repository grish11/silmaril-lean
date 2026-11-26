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
variable {vars before inside all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value vars}

private abbrev pack (m : Interpretation.{u,v,w} P) (store : Tuple m.Value vars) :
    Tuple (model m).Value (.bool :: vars) := .cons ⟨true⟩ store

private theorem guardFromFlag (test : Option (ULift.{w} Bool)) {flag : Bool}
    (h : test.map (fun b => !b.down) = some (!flag)) : test = some ⟨flag⟩ := by
  cases test with
  | none => cases h
  | some actual =>
    obtain ⟨actual⟩ := actual
    cases actual <;> cases flag <;> simp_all

/-- Decode the finite pass using the token at each successor sample to
justify the complete body step at the current one. -/
private theorem traceFromCompletion {read : Reads (model m) all}
    {init : Tuple (Port before) (.bool :: vars)}
    {code : Code (Opcode P) vars ((.bool :: vars) ++ before) inside}
    {cond : Port inside .bool} {next : Tuple (Port inside) (.bool :: vars)}
    {neg : Opcode P [.bool] .bool}
    (view : View (model m) env read [] (.loop init code cond next neg)) (i : Index all.length)
    (test : Expr P vars .bool) (body : Stmt P true vars vars)
    (flag : ∀ {j store}, AtIteration view i j (pack m store) →
      flags view i j = (test.eval m store).map (fun b => !b.down))
    (step : ∀ {j store}, AtIteration view i j (pack m store) →
      (samples view i .head (j + 1)).isSome →
      ∃ next, Exec m body store (some next) ∧ AtIteration view i (j + 1) (pack m next))
    (start count : Nat) {store : Tuple m.Value vars} (aligned : AtIteration view i start (pack m store))
    (stop : flags view i (start + count) = some true)
    (prior : ∀ j < count, flags view i (start + j) = some false)
    (defined : ∀ j ≤ count, (samples view i .head (start + j)).isSome) :
    ∃ final, WhileTrace m test body count store final := by
  induction count generalizing start store with
  | zero =>
    rw [Nat.add_zero, flag aligned] at stop
    exact ⟨store, .stop (guardFromFlag _ (flag := false) stop)⟩
  | succ count ih =>
    have continues := prior 0 (Nat.zero_lt_succ _)
    rw [Nat.add_zero, flag aligned] at continues
    obtain ⟨next, run, progressed⟩ := step aligned (defined 1 (by omega))
    have offset (j : Nat) : start + 1 + j = start + (j + 1) := by omega
    obtain ⟨final, rest⟩ := ih (start + 1) progressed
      (by rwa [offset]) (fun j hj => by rw [offset]; exact prior (j + 1) (by omega))
      (fun j hj => by rw [offset]; exact defined (j + 1) (by omega))
    exact ⟨final, .step (guardFromFlag _ (flag := true) continues) run rest⟩

theorem correspondence (guard : Expr P vars .bool) (body : Body P vars vars) (ret : Port vars t)
    (neg : P [.bool] .bool) (m : Interpretation.{u,v,w} P) (env : Tuple m.Value vars)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {val : (translate guard body ret neg).Valuation (model m)}
    (solves : (translate guard body ret neg).Solves (model m) env val)
    (i : Index (program guard body ret neg).nodes.length) :
    let observed := (translate guard body ret neg).observe (model m) val i
    (∀ {value}, (source guard body ret).Returns m env value →
      observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) ∧
    ((observed.get (.tail .head)).isSome → ∃ value, (source guard body ret).Returns m env value ∧
      observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) := by
  let compiled := program guard body ret neg
  let initial := entry P vars
  let slots := loopSlots vars initial.nodes
  let test := (expr guard).lower (params := vars) (tail slots)
  let step := body.lower (params := vars) (test.code.liftRefs slots)
  let loopCode := Code.loop initial.refs (.seq (.straight test.code) (.straight step.code))
    (step.code.lift (test.refs.get .head)) step.refs (.source neg)
  let read : Reads (model m) compiled.nodes := graphRead (model m) compiled.code compiled.refs val
  let v : View (model m) env read [] (.seq (.straight initial.code) loopCode) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations (model m) env compiled.code compiled.refs solves⟩
  have initialStore : RealizesOn read (fun r => v.right.embed (loopCode.lift r)) initial.refs
      (pack m env) [] i := by
    intro j _ ty slot
    refine (v.left.straightRead j (initial.refs.get slot)).trans ?_
    cases slot with
    | head => rfl
    | tail slot =>
      have value := Simple.Proofs.param_correct (model m) env (ports vars) .nil _ slot
      rw [get_select, ports_get] at value
      simp only [initial, entry, Simple.Code.eval, Tuple.get, get_map]
      exact value
  have guardAt {k store} (carries : AtIteration v.right i k (pack m store))
      (j : Index compiled.nodes.length) (agree : Agrees [] i j) :
      read (v.right.inner.left.embed (test.refs.get .head)) (j.set v.right.key k) =
        guard.eval m store := by
    let point := j.set v.right.key k
    have aligned := carries point (sampleAgrees v.right agree k)
    have data : RealizesAt read (fun r => v.right.inner.left.embed (test.code.lift r))
        (tail slots) store point := fun ty slot => aligned ty (.tail slot)
    exact (v.right.inner.left.straightRead point (test.refs.get .head)).trans
      (exprExact m env guard (tail slots) (v.right.inner.left.seed point) store
        (v.right.inner.left.seedRealizes data))
  have bodyAt {k store} (carries : AtIteration v.right i k (pack m store)) :
      match body.source.runLoopFree m store with
      | none => ∀ j, Agrees [v.right.key] (i.set v.right.key k) j →
          read (v.right.inner.embed (step.refs.get .head)) j = none
      | some next => RealizesOn read v.right.inner.embed step.refs (pack m next)
          [v.right.key] (i.set v.right.key k) := by
    have entryAt (j) (agree : Agrees [v.right.key] (i.set v.right.key k) j) :
        RealizesAt read (fun r => v.right.inner.right.embed (step.code.lift r))
          (test.code.liftRefs slots) (pack m store) j := by
      intro ty slot
      simpa only [Simple.Code.liftRefs, slots, loopSlots, get_map, ports_get, Code.lift, View.right]
        using carries j agree ty slot
    have exactAt (j) (agree : Agrees [v.right.key] (i.set v.right.key k) j) :=
      bodyExact m env body (test.code.liftRefs slots) (v.right.inner.right.seed j) ⟨true⟩ store
        (v.right.inner.right.seedRealizes (entryAt j agree))
    cases ran : body.source.runLoopFree m store with
    | none =>
      intro j agree
      exact (v.right.inner.right.straightRead j (step.refs.get .head)).trans
        (by simpa only [ran] using exactAt j agree)
    | some next =>
      intro j agree ty slot
      have realizes : Realizes (model m)
          (step.code.eval (model m) env (v.right.inner.right.seed j)) step.refs (pack m next) := by
        simpa only [ran] using exactAt j agree
      exact (v.right.inner.right.straightRead j (step.refs.get slot)).trans (realizes ty slot)
  have forward {value : m.Value t} (run : (source guard body ret).Returns m env value) :
      (translate guard body ret neg).observe (model m) val i =
        .cons (some value) (.cons (some ⟨true⟩) .nil) := by
    obtain ⟨final, ran, returned⟩ := run
    obtain ⟨count, trace⟩ := ran.while_trace
    have exit := traceExit v.right (pack m) negSem i
      (fun aligned eq j agree => (guardAt aligned j agree).trans eq)
      (fun {k store next} aligned bodyExec => by
        have bodyEval := (body.source.runLoopFree_enableWhile store).deterministic bodyExec
        have h := bodyAt aligned
        rw [bodyEval] at h
        exact h)
      trace 0 (atEntry v.right initialStore)
    have data := evalValue v.right exit i (agrees_self [] i) (.tail ret)
    have done := evalValue v.right exit i (agrees_self [] i) .head
    let lowered := (loop guard body neg initial.refs (params := vars)).refs
    change Tuple.cons (F := fun t => Option ((model m).Value t)) (read (lowered.get (.tail ret)) i)
      (.cons (read (lowered.get .head) i) .nil) = _
    simp only [lowered, loop, get_map, ports_get]
    change read (portLeft (.tail ret)) i = some (final.get ret) at data
    change read (portLeft .head) i = some ⟨true⟩ at done
    change final.get ret = value at returned
    rw [data, done, returned]
  refine ⟨@forward, ?_⟩
  intro done
  change (read (v.right.embed (portLeft .head)) i).isSome at done
  rw [evalEquation v.right i .head, passEquation v.right i] at done
  cases countEq : firstTrue (flags v.right i) with
  | none => simp [countEq] at done
  | some count =>
    rw [countEq] at done
    change (monotonize (samples v.right i .head) count).isSome at done
    obtain ⟨stop, prior⟩ := (firstTrue_eq_some_iff_samples _ _).mp countEq
    have tokenPrefix (j : Nat) (le : j ≤ count) : (samples v.right i .head j).isSome := by
      cases tok : monotonize (samples v.right i .head) count with
      | none => simp [tok] at done
      | some b =>
        obtain ⟨last, earlier⟩ := (monotonize_eq_some_iff _ _ _).mp tok
        rcases Nat.lt_or_eq_of_le le with lt | rfl
        · exact earlier _ lt
        · simp [last]
    have flag {k store} (aligned : AtIteration v.right i k (pack m store)) :
        flags v.right i k = (guard.eval m store).map (fun b => !b.down) := by
      unfold flags
      have atGuard := guardAt aligned i (agrees_self [] i)
      change read (v.right.inner.embed (step.code.lift (test.refs.get .head))) (i.set v.right.key k)
        = _ at atGuard
      rw [exitTestExact v.right negSem, atGuard]
      cases guard.eval m store <;> rfl
    have stepSound {k store} (aligned : AtIteration v.right i k (pack m store))
        (defined : (samples v.right i .head (k + 1)).isSome) :
        ∃ next, Exec m body.source.enableWhile store (some next) ∧
          AtIteration v.right i (k + 1) (pack m next) := by
      have h := bodyAt aligned
      cases run : body.source.runLoopFree m store with
      | none =>
        rw [run] at h
        rw [samples_succ, h _ (sampleAgrees v.right (agrees_self [] i) k)] at defined
        cases defined
      | some next =>
        rw [run] at h
        exact ⟨next, run ▸ body.source.runLoopFree_enableWhile store, stepIteration v.right h⟩
    obtain ⟨final, trace⟩ := traceFromCompletion v.right i guard body.source.enableWhile flag stepSound
      0 count (atEntry v.right initialStore) (by simpa only [Nat.zero_add] using stop)
      (by simpa only [Nat.zero_add] using prior) (by simpa only [Nat.zero_add] using tokenPrefix)
    have returns : (source guard body ret).Returns m env (final.get ret) := ⟨final, trace.exec, rfl⟩
    exact ⟨_, returns, forward returns⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Proofs
