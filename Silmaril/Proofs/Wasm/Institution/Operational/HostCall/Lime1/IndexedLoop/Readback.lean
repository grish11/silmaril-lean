module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Control
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
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

private theorem later_values {vs : List Value} (typed : p.later.TypedResult (.values vs)) :
    ∃ res : BitVec 32, vs = [i32 res] := by
  change vs.map Value.type = [.int .i32] at typed
  obtain ⟨resultValue, rest, rfl, resultType, tail⟩ := List.map_eq_cons_iff.mp typed
  obtain rfl : rest = [] := List.map_eq_nil_iff.mp tail
  obtain ⟨res, rfl⟩ := bits_of_type resultType
  exact ⟨res, rfl⟩

theorem live_step {a b : State} (move : Edge p mem host arg a b) (live : mem.Live a.bytes) : mem.Live b.bytes := by
  cases move <;> assumption

private theorem sound (checked : p.Checked mem outer index) {a b : State} (move : Edge p mem host arg a b) :
    Step host (p.render mem outer index arg a) (p.render mem outer index arg b) := by
  cases move with
  | control move => exact Step.of_internal ((internal_iff checked _).mpr ⟨_, move, rfl⟩)
  | producerReturns _ answer => exact Step.callout_returned (pending_producer checked) answer
  | producerTraps _ answer => exact Step.callout_returned (pending_producer checked) answer
  | producerDiverges answer => exact Step.callout_diverged (pending_producer checked) answer
  | laterReturns _ answer => exact Step.callout_returned (pending_later checked) answer
  | laterTraps _ answer => exact Step.callout_returned (pending_later checked) answer
  | laterDiverges answer => exact Step.callout_diverged (pending_later checked) answer

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

private theorem later_step (checked : p.Checked mem outer index) (contract : p.Contract mem host)
    (live : mem.Live bytes) (input : BitVec 32)
    (move : Step host (p.render mem outer index arg ⟨bytes, .laterInvoke input⟩) dst) :
    ∃ next, Edge p mem host arg ⟨bytes, .laterInvoke input⟩ next ∧
      dst = p.render mem outer index arg next := by
  have exactStep := Site.step_iff (site := p.later) (context := p.functionContext arg)
    (outer := outer) (dst := dst) (args := [i64 p.saved, i32 input]) checked.later contract.2 live rfl
  rcases exactStep.mp move with ⟨next, outcome, live, typed, answer, rfl⟩ | ⟨diverged, rfl⟩
  · cases outcome with
    | values vs =>
      obtain ⟨res, rfl⟩ := later_values typed
      exact ⟨⟨next, .bodyResult res⟩, .laterReturns live answer, rfl⟩
    | trap => exact ⟨⟨next, .bodyTrap [] []⟩, .laterTraps live answer, rfl⟩
  · exact ⟨_, .laterDiverges diverged, rfl⟩

private theorem internal_read (checked : p.Checked mem outer index) {a : Phase}
    (absent : decompose? (p.render mem outer index arg ⟨bytes, a⟩) = none)
    (move : Step host (p.render mem outer index arg ⟨bytes, a⟩) dst) :
    ∃ next, Edge p mem host arg ⟨bytes, a⟩ next ∧ dst = p.render mem outer index arg next := by
  have noCallout : ∀ call, ¬ CalloutAt (p.render mem outer index arg ⟨bytes, a⟩) call := by
    intro call located
    have found := exists_callout_iff.mp ⟨call, located⟩
    simp [absent] at found
  obtain ⟨next, edge, eq⟩ := (internal_iff checked a).mp ((Step.internal_iff_of_not_callout noCallout).mp move)
  exact ⟨⟨bytes, next⟩, .control edge, eq⟩

set_option backward.isDefEq.respectTransparency false in
theorem step_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a : State}
    (live : mem.Live a.bytes) :
    Step host (p.render mem outer index arg a) dst ↔
      ∃ next, Edge p mem host arg a next ∧ dst = p.render mem outer index arg next := by
  refine ⟨?_, ?_⟩
  swap
  · rintro ⟨_, edge, rfl⟩
    exact sound checked edge
  intro move
  rcases a with ⟨bytes, phase⟩
  have allocation : (mem.store bytes).funcs[p.rootAddress.value]? = some (.wasm signature p.module p.function) :=
    checked.root
  cases phase
  case producerInvoke input => exact producer_step checked contract live input move
  case laterInvoke input => exact later_step checked contract live input move
  all_goals
    refine internal_read checked ?_ move
    simp [decompose?, Program.render, Program.code, Program.functionCode, Program.loopCode,
      Program.function, Program.loop, Program.afterProducer, Program.afterLoop, Loops.LimeIndexedLoop.instr,
      resultCode, expression, decomposeFrom?_invoke_cons, Execution.Runtime.decomposeHead?, allocation, asValue?]
  all_goals split <;> simp_all

theorem run_iff (checked : p.Checked mem outer index) (contract : p.Contract mem host) {a : State}
    (live : mem.Live a.bytes) :
    Steps host (p.render mem outer index arg a) dst ↔
      ∃ next, Relation.ReflTransGen (Edge p mem host arg) a next ∧ mem.Live next.bytes ∧
        dst = p.render mem outer index arg next := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, live, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, path, live, rfl⟩ := ih
      obtain ⟨next, edge, rfl⟩ := (step_iff checked contract live).mp step
      exact ⟨next, path.tail edge, live_step edge live, rfl⟩
  · rintro ⟨next, path, nextLive, rfl⟩
    clear live nextLive
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail (sound checked edge)

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Proofs
