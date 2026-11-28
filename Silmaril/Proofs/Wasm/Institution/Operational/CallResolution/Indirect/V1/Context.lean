module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Context.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.V1.Execution.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.V1Context

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution
open CallContinuation.OuterCall.Ranked.Graph

theorem resolved_target {H : Type} {site : Site} {program : Memory32.Program} {m : MemAddr}
    {base : Store H} {initial : MemInst} (layout : Memory32.Layout program base m initial)
    {caller : Frame} (checked : site.V1Checked program base caller)
    {bytes : ByteArray} {selector : BitVec 32} {address : FuncAddr}
    (resolved : v1Resolve (Memory32.storeWithBytes base m initial bytes) caller site.typeIndex selector =
      some (.resolved address)) :
    ∃ fn, program.lookup address = some fn ∧ fn.declaration.type = site.signature := by
  have table : frameTable (Memory32.storeWithBytes base m initial bytes) caller = some site.table := checked.table
  cases entry : site.table.refs[selector.toNat]? with
  | none => simp [v1Resolve, resolveTable, table, entry] at resolved
  | some slot =>
    cases slot with
    | none => simp [v1Resolve, resolveTable, table, entry] at resolved
    | some target =>
      obtain ⟨fn, found⟩ := checked.targets target (List.mem_of_getElem? entry)
      have alloc : (Memory32.storeWithBytes base m initial bytes).funcs[target.value]? =
          some (.wasm fn.declaration.type fn.declaration.module fn.v1Func) := layout.functions target fn found
      by_cases same : fn.declaration.type = site.signature
      · simp [v1Resolve, resolveTable, table, entry, checked.signature, alloc, Execution.Runtime.FuncInst.type, same] at resolved
        subst target
        exact ⟨fn, found, same⟩
      · simp [v1Resolve, resolveTable, table, entry, checked.signature, alloc, Execution.Runtime.FuncInst.type, same] at resolved

private theorem rigid_step {H : Type} {a b : Config H} {saved : List Value} {tail : List Admin}
    (rigid : Rigid a.store a.code) (step : Step CallFrame.v1NoHost (v1Plug saved tail a) b) :
    ∃ next, Step CallFrame.v1NoHost a next ∧ b = v1Plug saved tail next := by
  rcases a with ⟨s, f, code⟩
  rcases b with ⟨t, g, after⟩
  obtain ⟨sameFrame, next, focused, eq⟩ := rigid.plug_inv .hole saved tail f g t after
    (by simpa only [v1Plug, plug_hole] using step)
  subst g
  refine ⟨⟨t, f, next⟩, focused f, ?_⟩
  rw [eq]
  rfl

theorem checked_step_iff {H : Type} {mode : Memory32.MemoryMode} {calls : Memory32.CallMode}
    {program : Memory32.Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : program.checkV1 m mode calls = true) (layout : Memory32.Layout program base m initial)
    (matched : mode.matches initial) {src : Memory32.State} {rank : Nat}
    (ready : Memory32.ReadyFor mode program m calls rank initial.data.size src)
    (rigid : Rigid (Memory32.render base m initial src).store src.code)
    {saved : List Value} {tail : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost (v1Plug saved tail (Memory32.render base m initial src)) dst ↔
      ∃ out, Memory32.EdgeAt mode program m src out ∧
        Memory32.ReadyFor mode program m calls rank initial.data.size out ∧
        dst = v1Plug saved tail (Memory32.render base m initial out) := by
  have exactStep (next : Config H) := Memory32.v1_step_iff_at (dst := next) checked layout matched ready
  constructor
  · intro move
    obtain ⟨next, focused, eq⟩ := rigid_step rigid move
    obtain ⟨out, edge, guarded, rfl⟩ := (exactStep next).mp focused
    exact ⟨out, edge, guarded, eq⟩
  · rintro ⟨out, edge, guarded, rfl⟩
    exact ((exactStep _).mpr ⟨out, edge, guarded, rfl⟩).context saved tail

private theorem factor {H : Type} {start dst : Config H} {saved : List Value} {tail : List Admin}
    (run : Steps CallFrame.v1NoHost start dst) :
    ∀ a : Config H, start = v1Plug saved tail a → Rigid a.store a.code →
      ∃ cut, Steps CallFrame.v1NoHost a cut ∧ v1CalleeEndpoint saved tail cut dst := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rintro a rfl rigid
    exact ⟨a, .refl, .inl ⟨rigid, rfl⟩⟩
  | head step rest ih =>
    rintro a rfl rigid
    obtain ⟨next, focused, plug⟩ := rigid_step rigid step
    rcases rigid.step_classify focused with live | result
    · obtain ⟨cut, callTrace, endpoint⟩ := ih next plug live
      exact ⟨cut, .head focused callTrace, endpoint⟩
    · exact ⟨next, .single focused, .inr ⟨result, plug ▸ rest⟩⟩

theorem run_iff {H : Type} {mode : Memory32.MemoryMode} {calls : Memory32.CallMode}
    {program : Memory32.Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (graph : program.checkV1 m mode calls = true) (layout : Memory32.Layout program base m initial)
    (matched : mode.matches initial) {site : Site} {caller : Frame}
    (checked : site.V1Checked program base caller)
    {bytes : ByteArray} (extent : mode.extent initial.data.size bytes)
    {selector : BitVec 32} {address : FuncAddr}
    (resolved : v1Resolve (Memory32.storeWithBytes base m initial bytes) caller site.typeIndex selector =
      some (.resolved address))
    {saved args : List Value} (typed : args.map Value.type = site.signature.params)
    {tail : List Admin} {dst : Config H} :
    let src := v1Source (Memory32.storeWithBytes base m initial bytes) caller site.typeIndex selector (saved ++ args) tail
    let invoke : Memory32.State := ⟨bytes, caller, values args ++ [.invoke address]⟩
    Steps CallFrame.v1NoHost src dst ↔ dst = src ∨
      ∃ fn, program.lookup address = some fn ∧ ∃ out, Memory32.RunsAt mode program m invoke out ∧
        Memory32.ReadyFor mode program m calls (fn.rank + 1) initial.data.size out ∧
        v1CalleeEndpoint saved tail (Memory32.render base m initial out) dst := by
  dsimp only
  obtain ⟨fn, found, signature⟩ := resolved_target layout checked resolved
  let pending : Memory32.State := ⟨bytes, caller, values args ++ [.invoke address]⟩
  have ready := Memory32.invoke_ready (p := program) (m := m) (calls := calls) (caller := caller) found args extent
  have count : args.length = fn.declaration.type.params.length := by
    rw [signature, ← typed, List.length_map]
  have rigid : Rigid (Memory32.render base m initial pending).store pending.code :=
    .invoke ⟨.wasm fn.declaration.type fn.declaration.module fn.v1Func, layout.functions address fn found, count⟩
  have plugEq :
      v1Resolved (Memory32.storeWithBytes base m initial bytes) caller (saved ++ args) tail (.resolved address) =
        v1Plug saved tail (Memory32.render base m initial pending) := by
    simp only [v1Resolved, Outcome.v1Head, v1Plug, Memory32.render, pending, values_append,
      List.append_assoc, List.singleton_append]
  have lookup := (v1_step_iff (host := CallFrame.v1NoHost)).mpr ⟨_, resolved, plugEq.symm⟩
  constructor
  · intro run
    rcases run.cases_head with same | ⟨next, step, rest⟩
    · exact .inl same.symm
    · obtain ⟨outcome, computed, eq⟩ := v1_step_iff.mp step
      rw [resolved] at computed
      cases computed
      rw [eq, plugEq] at rest
      obtain ⟨cut, callTrace, boundary⟩ := factor rest _ rfl rigid
      obtain ⟨out, trace, guarded, rfl⟩ := (Memory32.v1_run_iff_at graph layout matched ready).mp callTrace
      exact .inr ⟨fn, found, out, trace, guarded, boundary⟩
  · rintro (rfl | ⟨target, targetFound, out, trace, guarded, boundary⟩)
    · exact .refl
    · rw [found] at targetFound
      cases targetFound
      have call := (Memory32.v1_run_iff_at graph layout matched ready).mpr ⟨out, trace, guarded, rfl⟩
      have callTrace := (call.context saved tail).head lookup
      rcases boundary with ⟨_, rfl⟩ | ⟨_, rest⟩
      · exact callTrace
      · exact callTrace.trans rest

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.V1Context
