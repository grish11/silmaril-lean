module

public import Silmaril.Wasm.Institution.CoreComp.Thms

/-!
# Core modules and components in `GInst`: examples

A concrete sentence through the bridge: at the signature with one unknown core module `x`,
observed through every export (`oneVar`), the refinement `x ⊑ x` is valid in the core-module
logic over Core 3.0 (`refl_valid`). Its translation is therefore valid in `GInst`
(`refl_valid_GInst`, by `core3Module_valid_iff`), and conversely a `GInst` validity of a
translated sentence gives back validity in the module logic (`of_GInst`).
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.CoreComp.Examples

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Institution
open Silmaril.Wasm.Institution.Components Silmaril.Wasm.Component.Reference

/-- One unknown core module, observed through every export. -/
def oneVar : Sig compIfaces.I := ⟨Unit, Set.univ⟩

/-- `x ⊑ x`. -/
def refl (P : Profile) : (moduleSem (core3Sem P)).Sen oneVar :=
  ⟨Set.univ, 𝟙 _, .le (.var ()) (.var ())⟩

theorem refl_valid (P : Profile) : (moduleSem (core3Sem P)).Valid (refl P) :=
  (ObsSemantics.valid_iff _ _).2 fun _ => le_refl _

/-- **The translated sentence is valid in `GInst`.** -/
theorem refl_valid_GInst (P : Profile) :
    Silmaril.Inst.Institution.Valid (A := Silmaril.Games.GInst)
      ((core3ModuleToGInst P).sen oneVar (refl P)) :=
  (core3Module_valid_iff P (refl P)).1 fun β => (ObsSemantics.valid_iff _ _).1 (refl_valid P) β

/-- Conversely: a `GInst` validity of a translated module sentence is a module validity. -/
theorem of_GInst (P : Profile) (φ : (moduleSem (core3Sem P)).Sen oneVar)
    (h : Silmaril.Inst.Institution.Valid (A := Silmaril.Games.GInst)
      ((core3ModuleToGInst P).sen oneVar φ)) :
    (moduleSem (core3Sem P)).Valid φ :=
  (ObsSemantics.valid_iff _ _).2 fun β => (core3Module_valid_iff P φ).2 h β

end Silmaril.Wasm.Institution.CoreComp.Examples
