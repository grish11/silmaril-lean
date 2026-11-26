module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Control
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Proofs

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {p : Program H} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer : Frame} {index : FuncIdx} {arg : BitVec 64} {bytes : ByteArray} {dst : Config H}

private theorem bits_of_type {v : Value} {t : IntType} (typed : v.type = .int t) :
    ∃ bits : BitVec t.width, v = Value.int t bits := by
  cases v with
  | mk type bits =>
    cases typed
    exact ⟨bits, rfl⟩

private theorem producer_values {vs : List Value} (typed : p.producer.TypedResult (.values vs)) :
    ∃ (res : BitVec 32) (param : BitVec 64) (condition : BitVec 32), vs = [i32 res, i64 param, i32 condition] := by
  change vs.map Value.type = [.int .i32, .int .i64, .int .i32] at typed
  obtain ⟨resultValue, _, rfl, resultType, tail⟩ := List.map_eq_cons_iff.mp typed
  obtain ⟨paramValue, _, rfl, paramType, tail⟩ := List.map_eq_cons_iff.mp tail
  obtain ⟨flagValue, rest, rfl, flagType, last⟩ := List.map_eq_cons_iff.mp tail
  obtain rfl : rest = [] := List.map_eq_nil_iff.mp last
  obtain ⟨res, rfl⟩ := bits_of_type resultType
  obtain ⟨param, rfl⟩ := bits_of_type paramType
  obtain ⟨condition, rfl⟩ := bits_of_type flagType
  exact ⟨res, param, condition, rfl⟩

private theorem beforeContinuation {a b : Phase H} (move : Control arg p.saved p.continuation a b) :
    ∀ q labels, a ≠ .continuation q labels := by
  cases move <;> simp

private theorem preserves (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a b : State H}
    (move : Edge p mem host arg a b) (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes) :
    p.Ready mem host arg b.phase ∧ mem.Live b.bytes := by
  cases move with
  | control control =>
    refine ⟨?_, live⟩
    cases control with
    | loopResult => exact ⟨.nil, checked.continuation, contract.2⟩
    | exitLoop => exact ⟨.nil, trivial⟩
    | test => split <;> trivial
    | _ => trivial
  | producerReturns nextLive _ | producerTraps nextLive _ => exact ⟨trivial, nextLive⟩
  | producerDiverges _ => exact ⟨ready, live⟩
  | continuation edge => exact Continuation.preserves edge ready live

private theorem sound (checked : p.Checked mem outer index) {a b : State H}
    (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes) (move : Edge p mem host arg a b) :
    Step host (p.render mem outer index arg a) (p.render mem outer index arg b) := by
  cases move with
  | control move =>
    exact Step.of_internal ((internal_iff checked _ (beforeContinuation move)).mpr ⟨_, move, rfl⟩)
  | producerReturns _ answer => exact Step.callout_returned (pending_producer checked) answer
  | producerTraps _ answer => exact Step.callout_returned (pending_producer checked) answer
  | producerDiverges answer => exact Step.callout_diverged (pending_producer checked) answer
  | @continuation bytes next a b labels rest edge =>
    exact (Continuation.step_iff (mem := mem) (host := host) (outer := outer) (active := p.active arg)
      (results := p.functionResults) (a := ⟨bytes, a, labels⟩) (dst := p.render mem outer index arg ⟨next, .continuation b rest⟩)
      ready live).mpr ⟨_, edge, rfl⟩

private theorem producer_step (checked : p.Checked mem outer index) (contract : p.Contract mem host)
    (live : mem.Live bytes) (input : BitVec 64)
    (move : Step host (p.render mem outer index arg ⟨bytes, .producerInvoke input⟩) dst) :
    ∃ next, Edge p mem host arg ⟨bytes, .producerInvoke input⟩ next ∧
      dst = p.render mem outer index arg next := by
  have exactStep := Site.step_iff (site := p.producer) (context := p.producerContext arg)
    (outer := outer) (dst := dst) (args := [i64 input]) checked.producer contract.1 live rfl
  rcases exactStep.mp move with ⟨next, outcome, live, typed, answer, rfl⟩ | ⟨diverged, rfl⟩
  · cases outcome with
    | values vs =>
      obtain ⟨res, param, flag, rfl⟩ := producer_values typed
      exact ⟨⟨next, .test res param flag⟩, .producerReturns live answer, rfl⟩
    | trap => exact ⟨⟨next, .loopTrap Program.afterProducer⟩, .producerTraps live answer, rfl⟩
  · exact ⟨_, .producerDiverges diverged, rfl⟩

private theorem internal_read (checked : p.Checked mem outer index) {a : Phase H} (before : ∀ q labels, a ≠ .continuation q labels)
    (absent : decompose? (p.render mem outer index arg ⟨bytes, a⟩) = none)
    (move : Step host (p.render mem outer index arg ⟨bytes, a⟩) dst) :
    ∃ next, Edge p mem host arg ⟨bytes, a⟩ next ∧ dst = p.render mem outer index arg next := by
  have noCallout : ∀ call, ¬ CalloutAt (p.render mem outer index arg ⟨bytes, a⟩) call := by
    intro call located
    have found := exists_callout_iff.mp ⟨call, located⟩
    simp [absent] at found
  obtain ⟨next, edge, eq⟩ := (internal_iff checked a before).mp ((Step.internal_iff_of_not_callout noCallout).mp move)
  exact ⟨⟨bytes, next⟩, .control edge, eq⟩

set_option backward.isDefEq.respectTransparency false in
theorem step_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a : State H}
    (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes) :
    Step host (p.render mem outer index arg a) dst ↔
      ∃ next, Edge p mem host arg a next ∧ dst = p.render mem outer index arg next := by
  refine ⟨?_, ?_⟩
  swap
  · rintro ⟨_, edge, rfl⟩
    exact sound checked ready live edge
  intro move
  rcases a with ⟨bytes, phase⟩
  have allocation : (mem.store bytes).funcs[p.rootAddress.value]? = some (.wasm p.functionType p.module p.function) :=
    checked.root
  cases phase
  case producerInvoke input => exact producer_step checked contract live input move
  case continuation phase labels =>
    have theoremAtTail := Continuation.step_iff (mem := mem) (host := host) (outer := outer) (active := p.active arg)
      (results := p.functionResults) (a := ⟨bytes, phase, labels⟩) (dst := dst) ready live
    obtain ⟨next, edge, eq⟩ := theoremAtTail.mp move
    exact ⟨⟨next.bytes, .continuation next.phase next.labels⟩, .continuation edge, eq⟩
  all_goals
    refine internal_read checked (by simp) ?_ move
    simp [decompose?, Program.render, Program.code, Program.functionCode, Program.loopCode,
      Program.function, Program.loop, Program.afterProducer, Program.afterLoop, Loops.LimeIndexedLoop.instr,
      Continuation.entered, expression, decomposeFrom?_invoke_cons, Execution.Runtime.decomposeHead?, allocation,
      asValue?]

theorem run_sound (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a b : State H}
    (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes)
    (path : Relation.ReflTransGen (Edge p mem host arg) a b) :
    Steps host (p.render mem outer index arg a) (p.render mem outer index arg b) ∧
      p.Ready mem host arg b.phase ∧ mem.Live b.bytes := by
  induction path with
  | refl => exact ⟨.refl, ready, live⟩
  | tail _ edge ih =>
    obtain ⟨path, ready, live⟩ := ih
    exact ⟨path.tail (sound checked ready live edge), preserves checked contract edge ready live⟩

theorem run_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a : State H}
    (ready : p.Ready mem host arg a.phase) (live : mem.Live a.bytes) :
    Steps host (p.render mem outer index arg a) dst ↔
      ∃ next, Relation.ReflTransGen (Edge p mem host arg) a next ∧
        p.Ready mem host arg next.phase ∧ mem.Live next.bytes ∧ dst = p.render mem outer index arg next := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, ready, live, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, path, ready, live, rfl⟩ := ih
      obtain ⟨next, edge, rfl⟩ := (step_iff checked contract ready live).mp step
      obtain ⟨nextReady, nextLive⟩ := preserves checked contract edge ready live
      exact ⟨next, path.tail edge, nextReady, nextLive, rfl⟩
  · rintro ⟨next, path, _, _, rfl⟩
    exact (run_sound checked contract ready live path).1

theorem call_run_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) :
    Steps host ⟨base, outer, values [i64 arg] ++ [.source (.call index)]⟩ dst ↔
      ∃ next, Relation.ReflTransGen (Edge p mem host arg) ⟨mem.initial.data, .source⟩ next ∧
        mem.Live next.bytes ∧ dst = p.render mem outer index arg next := by
  have entry : p.render mem outer index arg ⟨mem.initial.data, .source⟩ =
      (⟨base, outer, values [i64 arg] ++ [.source (.call index)]⟩ : Config H) := by
    simp only [Program.render, Program.code, mem.store_initial]
  rw [← entry]
  constructor
  · intro run
    obtain ⟨next, path, _, live, eq⟩ := (run_iff (a := ⟨mem.initial.data, .source⟩) checked contract trivial rfl).mp run
    exact ⟨next, path, live, eq⟩
  · rintro ⟨next, path, _, rfl⟩
    exact (run_sound (arg := arg) (a := ⟨mem.initial.data, .source⟩) checked contract trivial rfl path).1


end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Proofs
