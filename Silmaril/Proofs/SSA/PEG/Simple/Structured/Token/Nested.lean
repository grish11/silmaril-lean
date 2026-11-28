module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Nested.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Region

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Token.Proofs
open Simple.Proofs (get_map get_select ports_get)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer child before all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value outer}
variable {read : Reads (model m) all} {active : List (Fin all.length)}

/-- The child and commit share one activation boundary. The input is the
realized old outer tuple at that coordinate, including its incoming token. -/
theorem activationFacts (f : Form P outer child t) (neg : P [.bool] .bool)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ctx : Tuple (Port before) (.bool :: outer))
    (v : View (model m) env read active (f.activation neg ctx).code)
    (i : Index all.length) (store : Tuple m.Value outer)
    (entry : RealizesOn read (fun r => v.embed ((f.activation neg ctx).code.lift r))
      ctx (pack m store) active i) :
    let refs := (f.activation neg ctx).refs
    (∀ {final}, Exec m f.step store (some final) →
      RealizesOn read v.embed refs (pack m final) active i) ∧
    ((read (v.embed (refs.get .head)) i).isSome → ∃ final,
      Exec m f.step store (some final) ∧ RealizesOn read v.embed refs (pack m final) active i ∧
      ∃ count : Nat, read (v.left.embed (passRef (.bool :: child))) i = some ⟨count⟩ ∧
        read (v.left.embed (portLeft .head)) i = some ⟨true⟩) := by
  let call := f.childRegion neg ctx
  let post := f.commit.lower (params := outer) call.refs
  change View (model m) env read active (.seq call.code (.straight post.code)) at v
  let cv := v.left
  let pv := v.right
  let childFacts := loopFreeFacts f.childGuard f.childBody neg cv
  have captureAligned :
      RealizesOn read (fun r => cv.embed (call.code.lift r)) (captureRefs f.capture ctx)
        (pack m (select store f.capture)) active i := by
    intro j agree ty slot
    cases slot with
    | head => exact entry j agree _ .head
    | tail p =>
      change read (cv.embed (call.code.lift ((select (tail ctx) f.capture).get p))) j =
        some ((select store f.capture).get p)
      rw [get_select, get_select]
      have ref : (tail ctx).get (f.capture.get p) = ctx.get (.tail (f.capture.get p)) := by
        cases ctx
        rfl
      rw [ref]
      exact entry j agree _ (.tail (f.capture.get p))
  have commitAt {final : Tuple m.Value child}
      (exits : RealizesOn read cv.embed call.refs (pack m final) active i) :
      match f.commit.source.runLoopFree m final with
      | none => ∀ j, Agrees active i j → read (v.embed (post.refs.get .head)) j = none
      | some next => RealizesOn read v.embed post.refs (pack m next) active i :=
    sliceExact f.commit call.refs pv final exits
  constructor
  · intro result run
    cases run with
    | seq project rest =>
      cases project
      cases rest with
      | seq childRun committed =>
        obtain ⟨_, trace⟩ := childRun.while_trace
        have exits := (LoopFacts.ofTrace cv childFacts negSem captureAligned trace).1
        have eq := (f.commit.source.runLoopFree_enableWhile _).deterministic committed
        have realized := commitAt exits
        rw [eq] at realized
        exact realized
  · intro complete
    have childComplete : (read (cv.embed (portLeft .head)) i).isSome := by
      cases token : read (cv.embed (portLeft .head)) i with
      | some b => rfl
      | none =>
        have noToken : read (v.embed (post.refs.get .head)) i = none := by
          apply sliceBottom f.commit call.refs pv
          change read (cv.embed (call.refs.get .head)) i = none
          simpa only [call, Form.childRegion, loop, get_map, ports_get] using token
        change (read (v.embed (post.refs.get .head)) i).isSome at complete
        rw [noToken] at complete
        cases complete
    obtain ⟨count, childFinal, trace, pass, _⟩ :=
      LoopFacts.ofCompletion cv childFacts negSem captureAligned childComplete
    have exits := (LoopFacts.ofTrace cv childFacts negSem captureAligned trace).1
    have atCommit := commitAt exits
    change (read (v.embed (post.refs.get .head)) i).isSome at complete
    cases ran : f.commit.source.runLoopFree m childFinal with
    | none =>
      rw [ran] at atCommit
      rw [atCommit _ (agrees_self active i)] at complete
      cases complete
    | some final =>
      rw [ran] at atCommit
      have commitRun := ran ▸ f.commit.source.runLoopFree_enableWhile childFinal
      have marker := exits i (agrees_self active i) _ .head
      exact ⟨final, .seq .project (.seq trace.exec commitRun), atCommit, ⟨count, pass, marker⟩⟩

theorem nestedFacts (f : Form P outer child t) (neg : P [.bool] .bool)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {init : Tuple (Port before) (.bool :: outer)}
    (v : View (model m) env read active (f.region neg init).code) :
    let cv := v.inner.right.left
    LoopFacts v f.guard f.step (fun j => ∃ count : Nat,
      read (cv.embed (passRef (.bool :: child))) j = some ⟨count⟩ ∧
      read (cv.embed (portLeft .head)) j = some ⟨true⟩) := by
  let test := loopTest f.guard outer before
  let ctx := test.code.liftRefs (loopSlots outer before)
  let step := f.activation neg ctx
  change View (model m) env read active (.loop init (.seq (.straight test.code) step.code)
    (step.code.lift (test.refs.get .head)) step.refs (.source neg)) at v
  have atActivation {i k store} (aligned : AtIteration v i k (pack m store)) :=
    activationFacts f neg negSem ctx v.inner.right (i.set v.key k) store
      (loopScopeAligned f.guard step.code v aligned)
  exact ⟨fun aligned j agree => guardAligned f.guard step.code v aligned j agree,
    fun aligned run => (atActivation aligned).1 run, fun aligned done => (atActivation aligned).2 done⟩

theorem correspondence (f : Form P outer child t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value outer)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {values : (f.translate neg).Valuation (model m)}
    (solves : (f.translate neg).Solves (model m) env values)
    (i : Index (f.program neg).nodes.length) :
    let observed := (f.translate neg).observe (model m) values i
    (∀ {value}, f.source.Returns m env value →
      observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) ∧
    ((observed.get (.tail .head)).isSome → ∃ count final,
      WhileTrace m f.guard f.step count env final ∧
      observed = .cons (some (final.get f.result)) (.cons (some ⟨true⟩) .nil) ∧
      (f.outerPass neg).read m.carrier (values ((f.outerPass neg).id, i)) = some ⟨count⟩ ∧
      ∀ j < count, ∃ trips, f.childExit neg m values (i.set (f.outerPass neg).id j) trips) := by
  let compiled := f.program neg
  let initial := entry P outer
  let lowered := f.region neg initial.refs
  let read : Reads (model m) compiled.nodes := graphRead (model m) compiled.code compiled.refs values
  let v : View (model m) env read [] (.seq (.straight initial.code) lowered.code) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations (model m) env compiled.code compiled.refs solves⟩
  let facts := nestedFacts f neg negSem v.right
  have start := entryAligned (fixed := i) v
  have forward {value : m.Value t} (run : f.source.Returns m env value) :
      (f.translate neg).observe (model m) values i = .cons (some value) (.cons (some ⟨true⟩) .nil) := by
    obtain ⟨final, ran, returned⟩ := run
    obtain ⟨_, trace⟩ := ran.while_trace
    have aligned := (LoopFacts.ofTrace v.right facts negSem start trace).1
    have data := aligned i (agrees_self [] i) _ (.tail f.result)
    have done := aligned i (agrees_self [] i) _ .head
    change Tuple.cons (F := fun t => Option ((model m).Value t)) (read (lowered.refs.get (.tail f.result)) i)
      (.cons (read (lowered.refs.get .head) i) .nil) = _
    change read (lowered.refs.get (.tail f.result)) i = some (final.get f.result) at data
    change read (lowered.refs.get .head) i = some ⟨true⟩ at done
    change final.get f.result = value at returned
    rw [data, done, returned]
  refine ⟨@forward, ?_⟩
  intro done
  change (read (v.right.embed (portLeft .head)) i).isSome at done
  obtain ⟨count, final, trace, pass, reached⟩ := LoopFacts.ofCompletion v.right facts negSem start done
  have returns : f.source.Returns m env (final.get f.result) := ⟨final, trace.exec, rfl⟩
  exact ⟨count, final, trace, forward returns, pass, reached⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Nested.Proofs
