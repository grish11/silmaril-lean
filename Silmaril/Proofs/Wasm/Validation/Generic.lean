module

public import Silmaril.Wasm.Validation.Generic.Defs

public section

namespace Silmaril.Proofs.Wasm.Validation.Generic

open Silmaril.Wasm Silmaril.Wasm.Generic Silmaril.Wasm.Validation

theorem raw_of_to (mod : RawModule Wasm.Func) : RawModule.ofCore mod.toCore = mod := by
  obtain ⟨metadata, empty, defs⟩ := mod
  cases metadata
  simp only at empty
  subst empty
  rfl

namespace Typed

open Silmaril.Wasm.Generic.Typed

variable {context : Context} {type : DefType} {types : List DefType} {interface : CModuleType}
  {F G K : FunctionFamily} {A B : Type}

theorem function_of_to (fn : Function Intrinsic.Body context type) : Function.ofIntrinsic fn.toIntrinsic = fn := by
  cases fn with
  | mk ref params results expands locals localTypes localValid body =>
    have same := (Validation.Inductive.Bounded.equiv (kind := .type_)).left_inv ref
    exact congrArg (fun ref => Function.mk ref params results expands locals localTypes localValid body) same

theorem function_to_of (fn : Intrinsic.Function context type) : (Function.ofIntrinsic fn).toIntrinsic = fn := by
  cases fn with
  | mk index resolves params results expands locals localTypes localValid body =>
    have same := (Validation.Inductive.Bounded.equiv (kind := .type_)).right_inv ⟨index, resolves⟩
    exact congrArg (fun ref : Intrinsic.Ref .type_ context.types type =>
      Intrinsic.Function.mk ref.index ref.resolves params results expands locals localTypes localValid body) same

theorem defs_of_to (defs : Definitions (Function Intrinsic.Body) context types) :
    Definitions.ofIntrinsic defs.toIntrinsic = defs := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.toIntrinsic, Definitions.ofIntrinsic, function_of_to, ih]

theorem defs_to_of (defs : Intrinsic.Functions context types) :
    (Definitions.ofIntrinsic defs).toIntrinsic = defs := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.toIntrinsic, Definitions.ofIntrinsic, function_to_of, ih]

theorem module_of_to (mod : Module (Function Intrinsic.Body) interface) :
    Module.ofIntrinsic mod.toIntrinsic = mod := by
  obtain ⟨⟨metadata, empty, types, signatures, tags, globals, tables, elems, typesValid, importsValid,
    tagsValid, globalsValid, memoriesValid, tablesValid, dataValid, elemsValid, startValid,
    exportsValid, exportsDisjoint⟩, defs⟩ := mod
  exact congrArg (Typed.Module.mk _) (defs_of_to defs)

theorem module_to_of (mod : Intrinsic.Module interface) : (Module.ofIntrinsic mod).toIntrinsic = mod := by
  obtain ⟨metadata, empty, types, tags, globals, tables, signatures, elems, _, _, typesValid,
    importsValid, rfl, rfl, tagsValid, globalsValid, memoriesValid, tablesValid, defs,
    dataValid, elemsValid, startValid, exportsValid, exportsDisjoint⟩ := mod
  exact congrArg (fun defs => Intrinsic.Module.mk metadata empty types tags globals tables signatures elems _ _
    typesValid importsValid rfl rfl tagsValid globalsValid memoriesValid tablesValid defs dataValid elemsValid
    startValid exportsValid exportsDisjoint) (defs_to_of defs)

theorem defs_map_id (defs : Definitions F context types) : defs.map (fun value => value) = defs := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.map, ih]

theorem defs_map_comp (f : ∀ {context type}, F context type → G context type)
    (g : ∀ {context type}, G context type → K context type) (defs : Definitions F context types) :
    (defs.map f).map g = defs.map (fun value => g (f value)) := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.map, ih]

theorem defs_get_map (f : ∀ {context type}, F context type → G context type)
    (defs : Definitions F context types) (path : Validation.Inductive.Path types type) :
    (defs.map f).get path = f (defs.get path) := by
  induction path with
  | here => cases defs; rfl
  | there path ih => cases defs; exact ih _

theorem defs_toList_get (f : ∀ {context type}, F context type → A) (defs : Definitions F context types)
    (path : Validation.Inductive.Path types type) :
    (defs.toList f)[path.toNat]? = some (f (defs.get path)) := by
  induction path with
  | here => cases defs; rfl
  | there path ih => cases defs; exact ih _

theorem defs_forget_map (f : ∀ {context type}, F context type → G context type)
    (erase : ∀ {context type}, G context type → A) (defs : Definitions F context types) :
    (defs.map f).toList erase = defs.toList (fun value => erase (f value)) := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.map, Definitions.toList, ih]

theorem defs_forget_natural (f : A → B) (erase : ∀ {context type}, F context type → A)
    (defs : Definitions F context types) : (defs.toList erase).map f = defs.toList (fun value => f (erase value)) := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.toList, ih]

theorem defs_erase (defs : Definitions (Function Intrinsic.Body) context types) :
    defs.toList Function.erase = defs.toIntrinsic.erase := by
  induction defs with
  | nil => rfl
  | cons head tail ih => simp [Definitions.toList, Definitions.toIntrinsic, Intrinsic.Functions.erase, ih]; rfl

end Typed
end Silmaril.Proofs.Wasm.Validation.Generic
