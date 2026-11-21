module

public import Silmaril.Wasm.Profiles.Defs
public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.ModuleParts.Thms
import Silmaril.Proofs.Wasm.Profiles.FunctionalCore

public section

namespace Silmaril.Wasm.Profiles

open Models

namespace Typing

variable {Raw Index : Type} {ok : Raw → Index → Prop}

@[expose] def declaredEquiv : Declared ok ≃ SomeChecked ok where
  toFun term := ⟨term.val.2, term.val.1, term.property⟩
  invFun term := ⟨(term.2.val, term.1), term.2.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem declaredEquiv_index (term : Declared ok) : (declaredEquiv term).1 = term.val.2 := rfl

theorem Declared.forget_surjective : Function.Surjective (Declared.forget (ok := ok)) := by
  rintro ⟨raw, index, typed⟩
  exact ⟨⟨(raw, index), typed⟩, rfl⟩

theorem Declared.forget_eq_iff (left right : Declared ok) :
    left.forget = right.forget ↔ left.val.1 = right.val.1 := Subtype.ext_iff

end Typing

theorem wasm1_func_iff (ctx : HasTyping.Context Wasm1) (fn : Function Wasm1) :
    (∃ sig, HasTyping.funcOk ctx fn sig) ↔ V1.Validation.FuncValid ctx fn := Iff.rfl

theorem lime_func_iff (ctx : HasTyping.Context Lime) (fn : Function Lime) :
    (∃ sig, HasTyping.funcOk ctx fn sig) ↔ Lime1.Validation.FuncValid ctx fn := Iff.rfl

theorem SomeTypedModule.checked_surjective {W : Type} [HasSyntax W] [HasTyping W] [HasIntrinsic W] :
    Function.Surjective (SomeTypedModule.checked (W := W)) := by
  rintro ⟨iface, raw, valid⟩
  obtain ⟨typed, rfl⟩ := HasIntrinsic.moduleLift valid
  exact ⟨⟨iface, typed⟩, rfl⟩

theorem SomeTypedFunction.checked_surjective {W : Type} [HasSyntax W] [HasTyping W] [HasIntrinsic W]
    (ctx : HasTyping.Context W) : Function.Surjective (SomeTypedFunction.checked (W := W) (ctx := ctx)) := by
  rintro ⟨sig, raw, valid⟩
  obtain ⟨typed, rfl⟩ := HasIntrinsic.functionLift valid
  exact ⟨⟨sig, typed⟩, rfl⟩

noncomputable def wasm3ModuleEquiv (iface : HasTyping.Interface Wasm3) :
    Validation.Intrinsic.Module.Erasure iface ≃ CheckedModule Wasm3 iface :=
  Validation.Intrinsic.Module.equiv iface

noncomputable def wasm3FunctionEquiv (ctx : HasTyping.Context Wasm3) (sig : HasTyping.FuncType Wasm3) :
    Validation.Intrinsic.Function.Erasure ctx sig ≃ CheckedFunction Wasm3 ctx sig :=
  Validation.Intrinsic.Function.equiv ctx sig

def CoreImage.ofLE {S T : FeatureSet} (sub : S ≤ T) : CoreImage S ↪ CoreImage T where
  toFun mod := ⟨mod.val, module_mono sub mod.val mod.property⟩
  inj' := fun _ _ eq => Subtype.ext (congrArg (fun mod : CoreImage T => mod.val) eq)

namespace FunctionalCore

@[expose] def toCore (gc : GCMode) (exceptions : ExceptionMode) :
    Module (FunctionalCore gc exceptions) ↪ Wasm.Module where
  toFun := Subtype.val
  inj' := fun _ _ => Subtype.ext

@[simp] theorem toCore_val {gc : GCMode} {exceptions : ExceptionMode} (mod : Module (FunctionalCore gc exceptions)) :
    toCore gc exceptions mod = mod.val := rfl

@[expose] def ofLE {gc nextGC : GCMode} {exceptions nextExceptions : ExceptionMode}
    (sub : features gc exceptions ≤ features nextGC nextExceptions) :
    Module (FunctionalCore gc exceptions) ↪ Module (FunctionalCore nextGC nextExceptions) where
  toFun mod := ⟨mod.val, module_mono sub _ mod.property.1, mod.property.2⟩
  inj' := fun _ _ eq => Subtype.ext (congrArg (fun mod : Module (FunctionalCore nextGC nextExceptions) => mod.val) eq)

@[simp] theorem ofLE_val {gc nextGC : GCMode} {exceptions nextExceptions : ExceptionMode}
    (sub : features gc exceptions ≤ features nextGC nextExceptions) (mod : Module (FunctionalCore gc exceptions)) :
    (ofLE sub mod).val = mod.val := rfl

theorem features_le_core (gc : GCMode) (exceptions : ExceptionMode) : features gc exceptions ≤ v30 :=
  Proofs.Wasm.Profiles.FunctionalCore.features_le_core gc exceptions

theorem toCore_features {gc : GCMode} {exceptions : ExceptionMode} (mod : Module (FunctionalCore gc exceptions)) :
    Module.InFeat v30 (toCore gc exceptions mod) := module_mono (features_le_core gc exceptions) _ mod.property.1

theorem mutation_le (exceptions : ExceptionMode) : features .immutable exceptions ≤ features .mutable exceptions :=
  Proofs.Wasm.Profiles.FunctionalCore.mutation_le exceptions

@[expose] def allowMutation (exceptions : ExceptionMode) :
    Module (FunctionalCore .immutable exceptions) ↪ Module (FunctionalCore .mutable exceptions) :=
  ofLE (mutation_le exceptions)

@[expose] def allowExceptions (gc : GCMode) :
    Module (FunctionalCore gc .disabled) ↪ Module (FunctionalCore gc .internal) :=
  ofLE (remove_le (features gc .internal) .exn)

theorem inclusion_square (mod : Module Strict) :
    allowMutation .internal (allowExceptions .immutable mod) =
      allowExceptions .mutable (allowMutation .disabled mod) := Subtype.ext rfl

theorem resources_empty {gc : GCMode} {exceptions : ExceptionMode} (mod : Module (FunctionalCore gc exceptions)) :
    mod.val.imports = [] ∧ mod.val.memories = [] ∧ mod.val.tables = [] ∧ mod.val.globals = [] ∧
      mod.val.elems = [] ∧ mod.val.data = [] := Proofs.Wasm.Profiles.FunctionalCore.resources_empty mod

theorem exports_function {gc : GCMode} {exceptions : ExceptionMode} (mod : Module (FunctionalCore gc exceptions))
    {entry : Export} (mem : entry ∈ mod.val.exports) : ∃ idx, entry.index = .func idx :=
  Proofs.Wasm.Profiles.FunctionalCore.exports_function mod mem

theorem tags_empty {gc : GCMode} (mod : Module (FunctionalCore gc .disabled)) : mod.val.tags = [] :=
  Proofs.Wasm.Profiles.FunctionalCore.tags_empty mod

@[expose] def checkedToCore {gc : GCMode} {exceptions : ExceptionMode} (iface : Validation.CModuleType) :
    CheckedModule (FunctionalCore gc exceptions) iface ↪ CheckedModule Wasm3 iface where
  toFun mod := ⟨mod.val.val, mod.property⟩
  inj' := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun mod : CheckedModule Wasm3 iface => mod.val) eq))

/-- The typed Core image is exact; no new typing derivation is selected. -/
@[expose] def checkedEquiv (gc : GCMode) (exceptions : ExceptionMode) (iface : Validation.CModuleType) :
    CheckedModule (FunctionalCore gc exceptions) iface ≃
      { mod : Wasm.Module // accepts gc exceptions mod ∧ Validation.ModuleOk mod iface } where
  toFun mod := ⟨mod.val.val, mod.val.property, mod.property⟩
  invFun mod := ⟨⟨mod.val, mod.property.1⟩, mod.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end FunctionalCore

@[expose] def Strict.toFunctional : Module Strict ↪ Module Functional :=
  (FunctionalCore.allowMutation .disabled).trans (FunctionalCore.allowExceptions .mutable)

@[simp] theorem Strict.toFunctional_val (mod : Module Strict) : (toFunctional mod).val = mod.val := rfl

@[simp] theorem Strict.check?_complete (mod : Module Strict) : check? mod.val = some mod := by
  cases mod with | mk raw valid => exact dite_eq_left valid

theorem Strict.check?_sound {raw : Wasm.Module} {mod : Module Strict} (ok : check? raw = some mod) :
    raw = mod.val := by
  unfold check? FunctionalCore.check? at ok
  split at ok
  · exact congrArg (fun term : Module Strict => term.val) (Option.some.inj ok)
  · cases ok

/-- Exactly the well-typed Core image at this interface. The inverse retains
the same Core AST, without choosing an intrinsic typing derivation. -/
abbrev Strict.checkedEquiv := FunctionalCore.checkedEquiv .immutable .disabled

@[simp] theorem Strict.checkedEquiv_val {iface} (mod : CheckedModule Strict iface) :
    (checkedEquiv iface mod).val = mod.val.val := rfl

@[simp] theorem Strict.parts_toCore (mod : Module Strict) : (parts mod).toCore = mod.val := mod.val.toCore_split

end Silmaril.Wasm.Profiles
