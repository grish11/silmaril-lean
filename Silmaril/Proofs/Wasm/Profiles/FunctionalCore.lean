module

public import Silmaril.Wasm.Profiles.Defs
public import Silmaril.Wasm.Models.Syntax.Thms

public section

namespace Silmaril.Proofs.Wasm.Profiles.FunctionalCore

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Profiles
open Silmaril.Wasm.Profiles.FunctionalCore

theorem features_le_core (gc : GCMode) (exceptions : ExceptionMode) : features gc exceptions ≤ v30 := by
  have base : features gc .internal ≤ v30 := by
    cases gc with
    | mutable => exact functionalMutGC_le_v30
    | immutable => exact functional_le_functionalMutGC.trans functionalMutGC_le_v30
  cases exceptions with
  | internal => exact base
  | disabled => exact (remove_le (features gc .internal) .exn).trans base

theorem mutation_le (exceptions : ExceptionMode) : features .immutable exceptions ≤ features .mutable exceptions := by
  cases exceptions with
  | internal => exact functional_le_functionalMutGC
  | disabled =>
    apply Silmaril.Wasm.Models.le_iff.mpr
    intro cap admitted
    simp only [features, FeatureSet.has, FeatureSet.remove, Bool.and_eq_true] at admitted ⊢
    exact ⟨has_of_le functional_le_functionalMutGC admitted.1, admitted.2⟩

theorem resources_empty {gc : GCMode} {exceptions : ExceptionMode}
    (mod : Silmaril.Wasm.Profiles.Module (FunctionalCore gc exceptions)) :
    mod.val.imports = [] ∧ mod.val.memories = [] ∧ mod.val.tables = [] ∧ mod.val.globals = [] ∧
      mod.val.elems = [] ∧ mod.val.data = [] := by
  have closed := mod.property.2
  simp only [closedShape, Bool.and_eq_true, List.isEmpty_iff, and_assoc] at closed
  exact ⟨closed.1, closed.2.1, closed.2.2.1, closed.2.2.2.1, closed.2.2.2.2.1, closed.2.2.2.2.2.1⟩

theorem exports_function {gc : GCMode} {exceptions : ExceptionMode}
    (mod : Silmaril.Wasm.Profiles.Module (FunctionalCore gc exceptions))
    {entry : Export} (mem : entry ∈ mod.val.exports) : ∃ idx, entry.index = .func idx := by
  have closed := mod.property.2
  simp only [closedShape, Bool.and_eq_true, List.all_eq_true] at closed
  have onlyFunc := closed.2 entry mem
  cases shape : entry.index
  case func idx => exact ⟨idx, rfl⟩
  all_goals simp [shape] at onlyFunc

theorem tags_empty {gc : GCMode} (mod : Silmaril.Wasm.Profiles.Module (FunctionalCore gc .disabled)) :
    mod.val.tags = [] := by
  have noExn : (features gc .disabled).has .exn = false := not_has_remove (features gc .internal) .exn
  have admitted := mod.property.1
  simp only [Module.InFeat, Module.inFeatB, noExn, Bool.or_false, Bool.and_eq_true, and_assoc] at admitted
  exact List.isEmpty_iff.mp admitted.2.2.1

end Silmaril.Proofs.Wasm.Profiles.FunctionalCore
