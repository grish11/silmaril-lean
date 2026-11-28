module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Conditional.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Nested

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Conditional.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Token.Proofs
open Simple.Proofs (get_map)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer child before all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value outer}
variable {read : Reads (model m) all} {active : List (Fin all.length)}

/-- Both directions read the same conditional join. A surviving marker
justifies the selected statement and exposes a child exit only on take. -/
theorem choiceFacts (f : Form P outer child t) (neg : P [.bool] .bool)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ctx : Tuple (Port before) (.bool :: outer))
    (v : View (model m) env read active (f.choice neg ctx).build.code)
    (i : Index all.length) (store : Tuple m.Value outer)
    (entry : RealizesOn read (fun r => v.embed ((f.choice neg ctx).build.code.lift r))
      ctx (pack m store) active i) :
    let choice := f.choice neg ctx
    (∀ {final}, Exec m f.step store (some final) →
      RealizesOn read v.embed choice.build.refs (pack m final) active i) ∧
    ((read (v.embed (choice.build.refs.get .head)) i).isSome →
      ∃ final, Exec m f.step store (some final) ∧
        RealizesOn read v.embed choice.build.refs (pack m final) active i ∧
        ∃ selected : Bool, read (v.embed choice.decision) i = some ⟨selected⟩ ∧
          (selected = true → ∃ count : Nat, read (v.embed choice.childPass) i = some ⟨count⟩ ∧
            read (v.embed choice.childToken) i = some ⟨true⟩)) := by
  let test := (expr f.selectChild).lower (params := outer) (tail ctx)
  let shared := test.code.liftRefs ctx
  let yes := f.parent.activation neg shared
  let skipped := yes.code.liftRefs shared
  let no := f.skip.lower (params := outer) skipped
  let flag := no.code.lift (yes.code.lift (test.refs.get .head))
  let joined := phiNodes (P := Opcode P) (params := outer) flag (no.code.liftRefs yes.refs) no.refs
  change View (model m) env read active (.seq (.straight test.code)
    (.seq yes.code (.seq (.straight no.code) (.straight joined.code)))) at v
  let tv := v.left
  let yv := v.right.left
  let nv := v.right.right.left
  let jv := v.right.right.right
  have decision (j) (agree : Agrees active i j) :
      read (v.embed (joined.code.lift flag)) j = f.selectChild.eval m store := by
    have data : RealizesAt read (fun r => tv.embed (test.code.lift r)) (tail ctx) store j := by
      intro ty slot
      cases ctx with
      | cons _ _ => exact entry j agree ty (.tail slot)
    exact (tv.straightRead j (test.refs.get .head)).trans
      (exprExact m env f.selectChild (tail ctx) (tv.seed j) store (tv.seedRealizes data))
  have yesInput : RealizesOn read (fun r => yv.embed (yes.code.lift r)) shared (pack m store) active i := by
    intro j agree ty slot
    simp only [shared, Simple.Code.liftRefs, get_map]
    exact entry j agree ty slot
  have noInput : RealizesOn read (fun r => nv.embed (no.code.lift r)) skipped (pack m store) active i := by
    intro j agree ty slot
    simp only [skipped, Code.liftRefs, get_map]
    exact yesInput j agree ty slot
  have atJoin (j) {ty} (slot : Port (.bool :: outer) ty) :
      read (v.embed (joined.refs.get slot)) j =
        (read (v.embed (joined.code.lift flag)) j).elim none (fun b =>
          if b.down then read (yv.embed (yes.refs.get slot)) j else read (nv.embed (no.refs.get slot)) j) := by
    have h := phiViewRead flag (no.code.liftRefs yes.refs) no.refs jv j slot
    change read (v.embed (joined.refs.get slot)) j =
      (read (v.embed (joined.code.lift flag)) j).elim none (fun b =>
        if b.down then read (v.embed (joined.code.lift ((no.code.liftRefs yes.refs).get slot))) j
        else read (v.embed (joined.code.lift (no.refs.get slot))) j) at h
    have lifted : (no.code.liftRefs yes.refs).get slot = no.code.lift (yes.refs.get slot) := by
      simp only [Simple.Code.liftRefs, get_map]
    rw [lifted] at h
    exact h
  have joinYes {final} (pick : f.selectChild.eval m store = some ⟨true⟩)
      (data : RealizesOn read yv.embed yes.refs (pack m final) active i) :
      RealizesOn read v.embed joined.refs (pack m final) active i := by
    intro j agree ty slot
    change read (v.embed (joined.refs.get slot)) j = some ((pack m final).get slot)
    rw [atJoin j slot, decision j agree, pick]
    exact data j agree ty slot
  have joinNo {final} (pick : f.selectChild.eval m store = some ⟨false⟩)
      (data : RealizesOn read nv.embed no.refs (pack m final) active i) :
      RealizesOn read v.embed joined.refs (pack m final) active i := by
    intro j agree ty slot
    change read (v.embed (joined.refs.get slot)) j = some ((pack m final).get slot)
    rw [atJoin j slot, decision j agree, pick]
    exact data j agree ty slot
  have taken := Nested.Proofs.activationFacts f.parent neg negSem shared yv i store yesInput
  have bypass := sliceExact f.skip skipped nv store noInput
  constructor
  · intro final run
    cases run with
    | branchTrue picked ran => exact joinYes picked (taken.1 ran)
    | branchFalse picked ran =>
      have eq := (f.skip.source.runLoopFree_enableWhile store).deterministic ran
      rw [eq] at bypass
      exact joinNo picked bypass
  · intro completed
    change (read (v.embed (joined.refs.get .head)) i).isSome at completed
    rw [atJoin, decision i (agrees_self active i)] at completed
    cases selected : f.selectChild.eval m store with
    | none =>
      rw [selected] at completed
      cases completed
    | some bit =>
      rw [selected] at completed
      obtain ⟨bit⟩ := bit
      cases bit with
      | false =>
        change (read (nv.embed (no.refs.get .head)) i).isSome at completed
        cases ran : f.skip.source.runLoopFree m store with
        | none =>
          rw [ran] at bypass
          rw [bypass i (agrees_self active i)] at completed
          cases completed
        | some final =>
          rw [ran] at bypass
          refine ⟨final, .branchFalse selected (ran ▸ f.skip.source.runLoopFree_enableWhile store),
            joinNo selected bypass, false, (decision i (agrees_self active i)).trans selected, ?_⟩
          intro impossible
          cases impossible
      | true =>
        change (read (yv.embed (yes.refs.get .head)) i).isSome at completed
        obtain ⟨final, run, data, count, pass, marker⟩ := taken.2 completed
        exact ⟨final, .branchTrue selected run, joinYes selected data, true,
          (decision i (agrees_self active i)).trans selected, fun _ => ⟨count, pass, marker⟩⟩

theorem conditionalFacts (f : Form P outer child t) (neg : P [.bool] .bool)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {init : Tuple (Port before) (.bool :: outer)}
    (v : View (model m) env read active (f.region neg init).code) :
    let choice := f.iteration neg before
    let cv := v.inner.right
    LoopFacts v f.parent.guard f.step (fun j =>
      ∃ selected : Bool, read (cv.embed choice.decision) j = some ⟨selected⟩ ∧
        (selected = true → ∃ count : Nat, read (cv.embed choice.childPass) j = some ⟨count⟩ ∧
          read (cv.embed choice.childToken) j = some ⟨true⟩)) := by
  let test := loopTest f.parent.guard outer before
  let ctx := test.code.liftRefs (loopSlots outer before)
  let step := (f.iteration neg before).build
  change View (model m) env read active (.loop init (.seq (.straight test.code) step.code)
    (step.code.lift (test.refs.get .head)) step.refs (.source neg)) at v
  have atBranch {i k store} (aligned : AtIteration v i k (pack m store)) :=
    choiceFacts f neg negSem ctx v.inner.right (i.set v.key k) store
      (loopScopeAligned f.parent.guard step.code v aligned)
  exact ⟨fun aligned j agree => guardAligned f.parent.guard step.code v aligned j agree,
    fun aligned run => (atBranch aligned).1 run, fun aligned done => (atBranch aligned).2 done⟩

theorem correspondence (f : Form P outer child t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value outer)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {values : (f.translate neg).Valuation (model m)}
    (solves : (f.translate neg).Solves (model m) env values)
    (i : Index (f.program neg).nodes.length) :
    let roots := (f.translate neg).observe (model m) values i
    (∀ {value}, f.source.Returns m env value →
      roots = .cons (some value) (.cons (some ⟨true⟩) .nil)) ∧
    ((roots.get (.tail .head)).isSome → ∃ count final,
      WhileTrace m f.parent.guard f.step count env final ∧
      roots = .cons (some (final.get f.parent.result)) (.cons (some ⟨true⟩) .nil) ∧
      (f.outerPass neg).read m.carrier (values ((f.outerPass neg).id, i)) = some ⟨count⟩ ∧
      ∀ j < count, f.activation neg m values (i.set (f.outerPass neg).id j)) := by
  let compiled := f.program neg
  let initial := entry P outer
  let lowered := f.region neg initial.refs
  let read : Reads (model m) compiled.nodes := graphRead (model m) compiled.code compiled.refs values
  let v : View (model m) env read [] (.seq (.straight initial.code) lowered.code) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations (model m) env compiled.code compiled.refs solves⟩
  let facts := conditionalFacts f neg negSem v.right
  have start := entryAligned (fixed := i) v
  have forward {value : m.Value t} (run : f.source.Returns m env value) :
      (f.translate neg).observe (model m) values i = .cons (some value) (.cons (some ⟨true⟩) .nil) := by
    obtain ⟨final, ran, returned⟩ := run
    obtain ⟨_, trace⟩ := ran.while_trace
    have aligned := (LoopFacts.ofTrace v.right facts negSem start trace).1
    have data := aligned i (agrees_self [] i) _ (.tail f.parent.result)
    have done := aligned i (agrees_self [] i) _ .head
    change Tuple.cons (F := fun t => Option ((model m).Value t))
      (read (lowered.refs.get (.tail f.parent.result)) i) (.cons (read (lowered.refs.get .head) i) .nil) = _
    change read (lowered.refs.get (.tail f.parent.result)) i = some (final.get f.parent.result) at data
    change read (lowered.refs.get .head) i = some ⟨true⟩ at done
    change final.get f.parent.result = value at returned
    rw [data, done, returned]
  refine ⟨@forward, ?_⟩
  intro done
  change (read (v.right.embed (portLeft .head)) i).isSome at done
  obtain ⟨count, final, trace, pass, reached⟩ := LoopFacts.ofCompletion v.right facts negSem start done
  have returns : f.source.Returns m env (final.get f.parent.result) := ⟨final, trace.exec, rfl⟩
  exact ⟨count, final, trace, forward returns, pass, reached⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Conditional.Proofs
