module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Proofs

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics

private theorem headCall {H : Type} {P : Profile} {s : Store H} {f : Frame} {i : FuncIdx}
    {args : List Val} {dst : Config H} (h : Head P s f args (.plain (.call i)) dst) :
    ∃ a fn, f.module.funcs[i.toNat]? = some a ∧ s.funcs[a]? = some fn ∧
      dst = ⟨s, f, [.ref (.func a), .callRefType fn.type]⟩ := by
  cases h with
  | call index fn => exact ⟨_, _, index, fn, rfl⟩
  | _ =>
    first
    | have eq := (famOf_of_shape (ParametricStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (NumericStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (VectorStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (VariableStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (TableStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (MemoryStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (RefStep.shape ‹_›)).2; contradiction
    | have eq := (famOf_of_shape (AggregateStep.shape ‹_›)).2; contradiction
    | contradiction

private theorem nativeCall {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {i : FuncIdx} {dst : Config H} (step : Step P noHost ⟨s, f, [.plain (.call i)]⟩ dst) :
    ∃ a fn, f.module.funcs[i.toNat]? = some a ∧ s.funcs[a]? = some fn ∧
      dst = ⟨s, f, [.ref (.func a), .callRefType fn.type]⟩ := by
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with hd | hb
  · obtain ⟨saved, args, op, tail, _, eq, _, hh, rfl⟩ := fnv_headDec hd
    change ([], [.plain (.call i)]) = (saved ++ args, op :: tail) at eq
    simp only [Prod.mk.injEq, List.nil_eq_append_iff, List.cons.injEq] at eq
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := eq
    obtain ⟨a, fn, index, found, rfl⟩ := headCall hh
    exact ⟨a, fn, index, found, rfl⟩
  · obtain ⟨_, _, _, _, _, ⟨eq, _, _⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble hb <;>
      change (([] : List Val), [Admin.plain (.call i)]) = _ at eq <;> simp at eq

private theorem rendered_function {H : Type} {s : Wasm.Lime1.Execution.Store H}
    {a : Runtime.FuncAddr} {fn : Runtime.FuncInst Wasm.Lime1.Func H}
    (found : s.funcs[a.value]? = some fn) :
    s.toCore.funcs[a.value]? = some fn.toCore ∧ s.funcDefType a = fn.toCore.type := by
  constructor
  · simp [Runtime.Store.toCore, List.getElem?_map, found]
  · cases fn <;> simp [Runtime.Store.funcDefType, found, Runtime.FuncInst.type, Runtime.FuncInst.toCore]

theorem core_readback {H : Type} {P : Profile} {s : Wasm.Lime1.Execution.Store H} {f : Runtime.Frame}
    {i : FuncIdx} {dst : Config H} (h : Step P noHost (limeConfig s f (.call i)).toCore dst) :
    ∃ a, Edge f.module.funcs (.call i) (.invoke a) ∧ (s.funcs[a.value]?).isSome ∧
      dst = (limeConfig s f (.invoke a)).toCore := by
  obtain ⟨address, fn, index, found, rfl⟩ := nativeCall h
  change (f.module.funcs.map Runtime.Addr.value)[i.toNat]? = some address at index
  simp only [List.getElem?_map] at index
  cases atIndex : f.module.funcs[i.toNat]? with
  | none => simp [atIndex] at index
  | some a =>
    have equal : a.value = address := by simpa [atIndex] using index
    subst address
    change (s.funcs.map Runtime.FuncInst.toCore)[a.value]? = some fn at found
    simp only [List.getElem?_map] at found
    cases allocated : s.funcs[a.value]? with
    | none => simp [allocated] at found
    | some source =>
      have eq : source.toCore = fn := by simpa [allocated] using found
      subst fn
      refine ⟨a, resolves atIndex, by simp [allocated], ?_⟩
      change (⟨s.toCore, f.toCore, [.ref (.func a.value), .callRefType source.toCore.type]⟩ : Config H) =
        ⟨s.toCore, f.toCore, [.ref (.func a.value), .callRefType (s.funcDefType a)]⟩
      rw [(rendered_function allocated).2]

theorem core_sound {H : Type} {P : Profile} {s : Wasm.Lime1.Execution.Store H} {f : Runtime.Frame}
    {i : FuncIdx} (guard : Allocated s f i) {a : Runtime.FuncAddr}
    (edge : Edge f.module.funcs (.call i) (.invoke a)) :
    Step P noHost (limeConfig s f (.call i)).toCore (limeConfig s f (.invoke a)).toCore := by
  obtain ⟨j, b, sameCall, sameAddr, index⟩ := CallResolution.invert edge
  cases sameCall
  cases sameAddr
  have bind := guard _ index
  cases found : s.funcs[a.value]? with
  | none => simp [found] at bind
  | some fn =>
    have hx : f.toCore.module.funcs[i.toNat]? = some a.value := by
      simp [Runtime.Frame.toCore, Runtime.ModuleInst.toCore, List.getElem?_map, index]
    have ⟨hs, ht⟩ := rendered_function found
    change Step P noHost ⟨s.toCore, f.toCore, [.plain (.call i)]⟩
      ⟨s.toCore, f.toCore, [.ref (.func a.value), .callRefType (s.funcDefType a)]⟩
    rw [ht]
    exact .call hx hs

end Silmaril.Wasm.Institution.Operational.CallResolution.Proofs
