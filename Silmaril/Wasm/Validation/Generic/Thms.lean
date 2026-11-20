module

public import Silmaril.Wasm.Validation.Generic.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Thms
import Silmaril.Proofs.Wasm.Validation.Generic

public section

namespace Silmaril.Wasm.Generic

namespace RawModule

def coreEquiv : Wasm.Module ≃ RawModule Wasm.Func where
  toFun := ofCore
  invFun := toCore
  left_inv mod := by cases mod; rfl
  right_inv := Proofs.Wasm.Validation.Generic.raw_of_to

@[simp] theorem coreEquiv_toCore (mod : Wasm.Module) : (coreEquiv mod).toCore = mod :=
  coreEquiv.left_inv mod

theorem toCore_injective : Function.Injective (toCore : RawModule Wasm.Func → Wasm.Module) :=
  coreEquiv.symm.injective

@[simp] theorem map_id {F : Type} (mod : RawModule F) : mod.map id = mod := by
  cases mod; simp [map]

theorem map_comp {F G K : Type} (f : F → G) (g : G → K) (mod : RawModule F) :
    (mod.map f).map g = mod.map (g ∘ f) := by cases mod; simp [map, List.map_map]

@[simp] theorem coreEquiv_map (f : Wasm.Func → Wasm.Func) (mod : Wasm.Module) :
    coreEquiv { mod with funcs := mod.funcs.map f } = (coreEquiv mod).map f := by cases mod; rfl

theorem mapInstructions_coreEquiv (f : Instr → Instr) (mod : Wasm.Module) :
    (coreEquiv mod).mapInstructions f =
      coreEquiv { mod with funcs := mod.funcs.map (Declaration.Func.mapBody (List.map f)) } :=
  (coreEquiv_map _ _).symm

end RawModule

namespace Typed

open Validation

variable {context : Context} {type : DefType} {interface : CModuleType}
  {F G K : FunctionFamily} {B C D : BodyFamily} {A Z : Type}

def Function.intrinsicEquiv : Intrinsic.Function context type ≃ Function Intrinsic.Body context type where
  toFun := Function.ofIntrinsic
  invFun := Function.toIntrinsic
  left_inv := Proofs.Wasm.Validation.Generic.Typed.function_to_of
  right_inv := Proofs.Wasm.Validation.Generic.Typed.function_of_to

@[simp] theorem Function.map_id (fn : Function B context type) : fn.map (fun body => body) = fn := rfl

theorem Function.map_comp (f : ∀ {context sig}, B context sig → C context sig)
    (g : ∀ {context sig}, C context sig → D context sig) (fn : Function B context type) :
    (fn.map f).map g = fn.map (fun body => g (f body)) := rfl

@[simp] theorem Function.toIntrinsic_erase (fn : Function Intrinsic.Body context type) :
    fn.toIntrinsic.erase = fn.erase := rfl

theorem Function.intrinsicEquiv_erase (fn : Intrinsic.Function context type) :
    (Function.intrinsicEquiv fn).erase = fn.erase :=
  (Function.toIntrinsic_erase _).symm.trans (congrArg Intrinsic.Function.erase (Function.intrinsicEquiv.left_inv fn))

theorem Function.sound (fn : Function Intrinsic.Body context type) : FuncOk context fn.erase type :=
  fn.toIntrinsic.sound

theorem Function.lift_erase {raw : Wasm.Func} (valid : FuncOk context raw type) :
    ∃ fn : Function Intrinsic.Body context type, fn.erase = raw := by
  obtain ⟨fn, erased⟩ := Intrinsic.Function.lift_erase valid
  exact ⟨Function.ofIntrinsic fn, (Function.toIntrinsic_erase _).symm.trans
    ((congrArg Intrinsic.Function.erase (Function.intrinsicEquiv.left_inv fn)).trans erased)⟩

@[simp] theorem Definitions.get_map {types : List DefType}
    (f : ∀ {context type}, F context type → G context type) (defs : Definitions F context types)
    (path : Validation.Inductive.Path types type) : (defs.map f).get path = f (defs.get path) :=
  Proofs.Wasm.Validation.Generic.Typed.defs_get_map f defs path

@[simp] theorem Definitions.toList_get {types : List DefType}
    (f : ∀ {context type}, F context type → A) (defs : Definitions F context types)
    (path : Validation.Inductive.Path types type) :
    (defs.toList f)[path.toNat]? = some (f (defs.get path)) :=
  Proofs.Wasm.Validation.Generic.Typed.defs_toList_get f defs path

def Module.intrinsicEquiv : Intrinsic.Module interface ≃ Module (Function Intrinsic.Body) interface where
  toFun := Module.ofIntrinsic
  invFun := Module.toIntrinsic
  left_inv := Proofs.Wasm.Validation.Generic.Typed.module_to_of
  right_inv := Proofs.Wasm.Validation.Generic.Typed.module_of_to

@[simp] theorem Module.map_id (mod : Module F interface) : mod.map (fun fn => fn) = mod :=
  congrArg (Module.mk mod.header) (Proofs.Wasm.Validation.Generic.Typed.defs_map_id mod.defs)

theorem Module.map_comp (f : ∀ {context type}, F context type → G context type)
    (g : ∀ {context type}, G context type → K context type) (mod : Module F interface) :
    (mod.map f).map g = mod.map (fun fn => g (f fn)) :=
  congrArg (Module.mk mod.header) (Proofs.Wasm.Validation.Generic.Typed.defs_map_comp f g mod.defs)

theorem Module.forget_map (f : ∀ {context type}, F context type → G context type)
    (erase : ∀ {context type}, G context type → A) (mod : Module F interface) :
    (mod.map f).forget erase = mod.forget (fun fn => erase (f fn)) :=
  congrArg (RawModule.mk mod.header.metadata mod.header.noFunctions)
    (Proofs.Wasm.Validation.Generic.Typed.defs_forget_map f erase mod.defs)

theorem Module.forget_natural (f : A → Z) (erase : ∀ {context type}, F context type → A)
    (mod : Module F interface) : (mod.forget erase).map f = mod.forget (fun fn => f (erase fn)) :=
  congrArg (RawModule.mk mod.header.metadata mod.header.noFunctions)
    (Proofs.Wasm.Validation.Generic.Typed.defs_forget_natural f erase mod.defs)

/-- A commuting square for dependent function maps and raw function maps. -/
theorem Module.forget_commutes (f : ∀ {context type}, F context type → G context type)
    (rawMap : A → Z) (eraseF : ∀ {context type}, F context type → A)
    (eraseG : ∀ {context type}, G context type → Z)
    (square : ∀ {context type} (fn : F context type), eraseG (f fn) = rawMap (eraseF fn))
    (mod : Module F interface) : (mod.map f).forget eraseG = (mod.forget eraseF).map rawMap := by
  have same : (fun {context type} (fn : F context type) => eraseG (f fn)) =
      (fun {context type} (fn : F context type) => rawMap (eraseF fn)) := by funext; apply square
  rw [Module.forget_map, Module.forget_natural, same]

@[simp] theorem Module.forget_toCore (mod : Module (Function Intrinsic.Body) interface) :
    (mod.forget Function.erase).toCore = mod.erase := rfl

@[simp] theorem Module.toIntrinsic_erase (mod : Module (Function Intrinsic.Body) interface) :
    mod.toIntrinsic.erase = mod.erase :=
  congrArg (fun defs => { mod.header.metadata with funcs := defs })
    (Proofs.Wasm.Validation.Generic.Typed.defs_erase mod.defs).symm

theorem Module.sound (mod : Module (Function Intrinsic.Body) interface) : ModuleOk mod.erase interface := by
  simpa only [Module.toIntrinsic_erase] using mod.toIntrinsic.sound

theorem Module.lift_erase {raw : Wasm.Module} (valid : ModuleOk raw interface) :
    ∃ mod : Module (Function Intrinsic.Body) interface, mod.erase = raw := by
  obtain ⟨mod, erased⟩ := Intrinsic.Module.lift_erase valid
  exact ⟨Module.ofIntrinsic mod, (Module.toIntrinsic_erase _).symm.trans
    ((congrArg Intrinsic.Module.erase (Module.intrinsicEquiv.left_inv mod)).trans erased)⟩

theorem Module.intrinsicEquiv_erase (mod : Intrinsic.Module interface) :
    (Module.intrinsicEquiv mod).forget Function.erase = RawModule.coreEquiv mod.erase :=
  RawModule.coreEquiv.symm.injective <| (Module.forget_toCore _).trans
    ((Module.toIntrinsic_erase _).symm.trans
      (congrArg Intrinsic.Module.erase (Module.intrinsicEquiv.left_inv mod)))

end Typed
end Silmaril.Wasm.Generic
