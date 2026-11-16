module

public import Silmaril.Wasm.Institution.CoreComp.Defs
public import Silmaril.Wasm.Institution.GameReadings.Thms
public import Silmaril.Logic.Inst.Thms

/-!
# Core modules and components in `GInst`: theorems

* `reductionToGInst_modelExpansive`, `core3ModuleToGInst_modelExpansive`,
  `componentToGInst_modelExpansive`: the three comorphisms are model-expansive (each is a
  surjective translation into the game logic followed by the game reading, whose model maps are
  surjective: `GameInst.coHom_modelExpansive`);
* **borrowing**: `reduction_valid_iff`, `core3Module_valid_iff`, `component_valid_iff` (validity),
  and `core3Module_entails_iff` (entailment): a sentence holds in the source logic iff its
  translation holds in `GInst`.

All composed from existing results; short proofs inline.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.CoreComp

open Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Institution.Games Silmaril.Wasm.Institution.Components
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

theorem reductionToGInst_modelExpansive {H : Type} (P : Profile) (host : HostSemantics H) :
    (reductionToGInst P host).ModelExpansive :=
  Inst.CoHom.ModelExpansive.comp
    ((redToGame exportIfaces Silmaril.Games.Sig.empty (wasmRed P host)).coHom_modelExpansive
      fun _ σ => ⟨σ, rfl⟩)
    (GameInst.coHom_modelExpansive exportIfaces Silmaril.Games.Sig.empty)

theorem core3ModuleToGInst_modelExpansive (P : Profile) :
    (core3ModuleToGInst P).ModelExpansive :=
  Inst.CoHom.ModelExpansive.comp
    ((moduleToGame (core3Sem P)).coHom_modelExpansive fun _ σ => ⟨σ, rfl⟩)
    (GameInst.coHom_modelExpansive compIfaces sigU)

theorem componentToGInst_modelExpansive (P : Profile) :
    (componentToGInst P).ModelExpansive :=
  Inst.CoHom.ModelExpansive.comp
    ((compToGame (core3Sem P)).coHom_modelExpansive fun _ σ => ⟨σ, rfl⟩)
    (GameInst.coHom_modelExpansive compIfaces sigU)

/-- **Borrowing validity** from the reduction logic of Wasm instances into `GInst`. -/
theorem reduction_valid_iff {H : Type} (P : Profile) (host : HostSemantics H)
    {S : (redSem exportIfaces Silmaril.Games.Sig.empty (wasmRed P host)).inst.Sign} (φ) :
    Silmaril.Inst.Institution.Valid (A := (redSem exportIfaces Silmaril.Games.Sig.empty
      (wasmRed P host)).inst) (S := S) φ ↔
      Silmaril.Inst.Institution.Valid (A := Silmaril.Games.GInst)
        ((reductionToGInst P host).sen S φ) :=
  Silmaril.Inst.Comorphism.valid_iff _ (reductionToGInst_modelExpansive P host) φ

/-- **Borrowing validity** from the core-module logic over Core 3.0 into `GInst`. -/
theorem core3Module_valid_iff (P : Profile) {S : (moduleSem (core3Sem P)).inst.Sign} (φ) :
    Silmaril.Inst.Institution.Valid (A := (moduleSem (core3Sem P)).inst) (S := S) φ ↔
      Silmaril.Inst.Institution.Valid (A := Silmaril.Games.GInst) ((core3ModuleToGInst P).sen S φ) :=
  Silmaril.Inst.Comorphism.valid_iff _ (core3ModuleToGInst_modelExpansive P) φ

/-- **Borrowing validity** from the component logic over Core 3.0 into `GInst`. -/
theorem component_valid_iff (P : Profile) {S : (compSem (core3Sem P)).inst.Sign} (φ) :
    Silmaril.Inst.Institution.Valid (A := (compSem (core3Sem P)).inst) (S := S) φ ↔
      Silmaril.Inst.Institution.Valid (A := Silmaril.Games.GInst) ((componentToGInst P).sen S φ) :=
  Silmaril.Inst.Comorphism.valid_iff _ (componentToGInst_modelExpansive P) φ

/-- **Borrowing entailment** from the core-module logic over Core 3.0 into `GInst`. -/
theorem core3Module_entails_iff (P : Profile) (S : (moduleSem (core3Sem P)).inst.Sign) (Γ φ) :
    Silmaril.Inst.Institution.Entails (A := (moduleSem (core3Sem P)).inst) (S := S) Γ φ ↔
      Silmaril.Inst.Institution.Entails (A := Silmaril.Games.GInst)
        ((core3ModuleToGInst P).sen S '' Γ) ((core3ModuleToGInst P).sen S φ) :=
  Silmaril.Inst.Comorphism.entails_iff _ (core3ModuleToGInst_modelExpansive P) S Γ φ

end Silmaril.Wasm.Institution.CoreComp
