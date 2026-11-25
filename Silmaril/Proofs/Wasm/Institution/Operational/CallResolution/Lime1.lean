module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Thms
public import Silmaril.Wasm.Institution.Operational.CallResolution.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Proofs.Lime1

open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Execution.Runtime

private theorem pure_not_call {types : List Lime1.FuncType} {before after : List Admin} (h : PureStep types before after)
    (i : FuncIdx) (sub : List.Sublist before [.source (.call i)]) : False := by
  have ready := sub.subset
  cases h <;> simp [values, value, Value.int] at ready

theorem readback {H : Type} {host : HostSemantics H} {src dst : Config H} (h : Step host src dst)
    {i : FuncIdx} (sub : List.Sublist src.code [.source (.call i)]) :
    ∃ a, src.code = [.source (.call i)] ∧ src.frame.module.funcs[i.toNat]? = some a ∧
      dst = ⟨src.store, src.frame, [.invoke a]⟩ := by
  induction h with
  | pure s f h => exact (pure_not_call h i sub).elim
  | @context s s' f f' before after h saved tail ih =>
    have middle := (List.sublist_append_right (values saved) before).trans
      (List.sublist_append_left (values saved ++ before) tail)
    obtain ⟨a, eq, found, target⟩ := ih (middle.trans sub)
    have length := sub.length_le
    change before = _ at eq
    change (values saved ++ before ++ tail).length ≤ 1 at length
    simp [values, eq] at length
    have savedEmpty : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have tailEmpty : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved
    subst tail
    exact ⟨a, by simp [values, eq], found, by simpa [values] using target⟩
  | call s f x a found =>
    have index := sub.subset (List.Mem.head _)
    simp at index
    subst x
    exact ⟨a, rfl, found, rfl⟩
  | _ =>
    have ready := sub.subset
    simp [values] at ready

theorem step_iff {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {s : Wasm.Lime1.Execution.Store H} {f : Frame} {i : FuncIdx} {dst : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfig s f (.call i)) dst ↔
      ∃ a, Edge f.module.funcs (.call i) (.invoke a) ∧ dst = limeConfig s f (.invoke a) := by
  constructor
  · intro h
    obtain ⟨a, _, index, target⟩ := readback h (i := i) (List.Sublist.refl _)
    exact ⟨a, resolves index, target⟩
  · rintro ⟨a, edge, rfl⟩
    obtain ⟨_, _, call, addr, index⟩ := invert edge
    cases call
    cases addr
    exact .call s f _ _ index

end Silmaril.Wasm.Institution.Operational.CallResolution.Proofs.Lime1
