module

public import Silmaril.Wasm.Profiles.Tags
public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Models.FX.Defs
public import Silmaril.Wasm.V1.Validation.Modules
public import Silmaril.Wasm.V2.Validation.Modules
public import Silmaril.Wasm.Lime1.Validation.Modules
public import Silmaril.Wasm.Validation.Intrinsic.Thms
public import Silmaril.Wasm.ModuleParts.Defs

@[expose] public section

namespace Silmaril.Wasm.Profiles

open Models

class HasSyntax (W : Type) where
  Value : Type
  Instruction : Type
  Body : Type
  Function : Type
  Module : Type

abbrev Value (W : Type) [HasSyntax W] := HasSyntax.Value W
abbrev Instruction (W : Type) [HasSyntax W] := HasSyntax.Instruction W
abbrev Body (W : Type) [HasSyntax W] := HasSyntax.Body W
abbrev Function (W : Type) [HasSyntax W] := HasSyntax.Function W
abbrev Module (W : Type) [HasSyntax W] := HasSyntax.Module W

/-- These are the existing feature manifests. A manifest alone is not a
translation or a characterization of a version's native syntax. -/
class HasFeatures (W : Type) where
  features : FeatureSet

instance : HasFeatures Wasm1 := ⟨v10⟩
instance : HasFeatures Wasm2 := ⟨v20⟩
instance : HasFeatures Wasm3 := ⟨v30⟩
instance : HasFeatures Lime := ⟨lime1⟩
instance : HasFeatures FX := ⟨wasmFX⟩
def FunctionalCore.features (gc : GCMode) (exceptions : ExceptionMode) : FeatureSet :=
  let base := match gc with | .mutable => functionalMutGC | .immutable => functional
  match exceptions with | .internal => base | .disabled => base.remove .exn

instance (gc : GCMode) (exceptions : ExceptionMode) : HasFeatures (FunctionalCore gc exceptions) :=
  ⟨FunctionalCore.features gc exceptions⟩

instance : HasSyntax Wasm1 := ⟨V1.ValType, V1.Instr, V1.Expr, V1.Func, V1.Module⟩
instance : HasSyntax Wasm2 := ⟨V2.ValType, V2.Instr, V2.Expr, V2.Func, V2.Module⟩
instance : HasSyntax Wasm3 := ⟨ValType, Instr, Expr, Func, Wasm.Module⟩
instance : HasSyntax Lime := ⟨Lime1.ValType, Lime1.Instr, Lime1.Expr, Lime1.Func, Lime1.Module⟩

/-- The existing FX model still loads a Core module. Extended function code
is stored separately in bindings keyed by host code. -/
instance : HasSyntax FX := ⟨ValType, Models.FX.InstrFX, List Models.FX.InstrFX, Models.FX.FuncFX, Wasm.Module⟩

structure FX.WithBindings (HostCode : Type) where
  core : Module FX
  bindings : HostCode → Option (Function FX)

def FX.WithBindings.ofCore {H : Type} (core : Module Wasm3) : WithBindings H := ⟨core, Models.FX.noFX⟩

/-- A dialect's actual typing judgments. Unit is used only for a judgment
which validates a module without an explicit interface index. -/
class HasTyping (W : Type) [HasSyntax W] where
  Context : Type
  FuncType : Type
  Interface : Type
  funcOk : Context → Function W → FuncType → Prop
  moduleOk : Module W → Interface → Prop

instance : HasTyping Wasm1 where
  Context := V1.Validation.Context
  FuncType := V1.FuncType
  Interface := Unit
  funcOk context fn sig := context.types[fn.type.toNat]? = some sig ∧ V1.Validation.FuncTypeValid sig ∧
    V1.Validation.ExprType (V1.Validation.functionContext context sig fn.locals) fn.body [] sig.results
  moduleOk mod _ := V1.Validation.ModuleValid mod

instance : HasTyping Wasm2 where
  Context := V2.Validation.Context
  FuncType := V2.FuncType
  Interface := List V2.ExternType × List V2.ExternType
  funcOk := V2.Validation.FuncOk
  moduleOk mod ports := V2.Validation.ModuleOk mod ports.1 ports.2

instance : HasTyping Wasm3 where
  Context := Validation.Context
  FuncType := Validation.DefType
  Interface := Validation.CModuleType
  funcOk := Validation.FuncOk
  moduleOk := Validation.ModuleOk

instance : HasTyping Lime where
  Context := Lime1.Validation.Context
  FuncType := Lime1.FuncType
  Interface := Unit
  funcOk context fn sig := context.types[fn.type.toNat]? = some sig ∧ Lime1.Validation.FuncTypeValid sig ∧
    Lime1.Validation.ExprType (Lime1.Validation.functionContext context sig fn.locals) fn.body [] sig.results
  moduleOk mod _ := Lime1.Validation.ModuleValid mod

namespace Typing

variable {Raw Index : Type}

abbrev Checked (ok : Raw → Index → Prop) (index : Index) := { raw : Raw // ok raw index }
abbrev SomeChecked (ok : Raw → Index → Prop) := Σ index, Checked ok index
abbrev Declared (ok : Raw → Index → Prop) := { pair : Raw × Index // ok pair.1 pair.2 }
abbrev Accepted (ok : Raw → Index → Prop) := { raw : Raw // ∃ index, ok raw index }

def Declared.forget {ok : Raw → Index → Prop} (term : Declared ok) : Accepted ok :=
  ⟨term.val.1, term.val.2, term.property⟩

end Typing

abbrev CheckedModule (W : Type) [HasSyntax W] [HasTyping W] := Typing.Checked (HasTyping.moduleOk (W := W))
abbrev DeclaredModule (W : Type) [HasSyntax W] [HasTyping W] := Typing.Declared (HasTyping.moduleOk (W := W))
abbrev ValidModule (W : Type) [HasSyntax W] [HasTyping W] := Typing.Accepted (HasTyping.moduleOk (W := W))
abbrev CheckedFunction (W : Type) [HasSyntax W] [HasTyping W] (ctx : HasTyping.Context W) :=
  Typing.Checked (HasTyping.funcOk ctx)

/-- A genuine intrinsic family can be added independently of the native
syntax/typing instances. Its erasure must be sound and cover the judgment. -/
class HasIntrinsic (W : Type) [HasSyntax W] [HasTyping W] where
  ModuleAt : HasTyping.Interface W → Type
  FunctionAt : HasTyping.Context W → HasTyping.FuncType W → Type
  eraseModule : ∀ {iface}, ModuleAt iface → Module W
  eraseFunction : ∀ {ctx sig}, FunctionAt ctx sig → Function W
  moduleSound : ∀ {iface} (term : ModuleAt iface), HasTyping.moduleOk (eraseModule term) iface
  functionSound : ∀ {ctx sig} (term : FunctionAt ctx sig), HasTyping.funcOk ctx (eraseFunction term) sig
  moduleLift : ∀ {iface raw}, HasTyping.moduleOk raw iface → ∃ term : ModuleAt iface, eraseModule term = raw
  functionLift : ∀ {ctx sig raw}, HasTyping.funcOk ctx raw sig →
    ∃ term : FunctionAt ctx sig, eraseFunction term = raw

instance : HasIntrinsic Wasm3 where
  ModuleAt := Validation.Intrinsic.Module
  FunctionAt := Validation.Intrinsic.Function
  eraseModule := Validation.Intrinsic.Module.erase
  eraseFunction := Validation.Intrinsic.Function.erase
  moduleSound := Validation.Intrinsic.Module.sound
  functionSound := Validation.Intrinsic.Function.sound
  moduleLift := Validation.Intrinsic.Module.lift_erase
  functionLift := Validation.Intrinsic.Function.lift_erase

abbrev TypedModule (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W] := HasIntrinsic.ModuleAt (W := W)
abbrev TypedFunction (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W] := HasIntrinsic.FunctionAt (W := W)
abbrev SomeTypedModule (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W] := Σ iface, TypedModule W iface
abbrev SomeTypedFunction (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W] (ctx : HasTyping.Context W) :=
  Σ sig, TypedFunction W ctx sig

def SomeTypedModule.checked {W : Type} [HasSyntax W] [HasTyping W] [HasIntrinsic W]
    (term : SomeTypedModule W) : Typing.SomeChecked (HasTyping.moduleOk (W := W)) :=
  ⟨term.1, HasIntrinsic.eraseModule term.2, HasIntrinsic.moduleSound term.2⟩

def SomeTypedFunction.checked {W : Type} [HasSyntax W] [HasTyping W] [HasIntrinsic W] {ctx : HasTyping.Context W}
    (term : SomeTypedFunction W ctx) : Typing.SomeChecked (HasTyping.funcOk ctx) :=
  ⟨term.1, HasIntrinsic.eraseFunction term.2, HasIntrinsic.functionSound term.2⟩

/-- An exact restriction of the Core AST, not the native AST of an earlier version. -/
abbrev CoreImage (S : FeatureSet) := { mod : Wasm.Module // Module.InFeat S mod }

def CoreImage.check? (S : FeatureSet) (mod : Wasm.Module) : Option (CoreImage S) :=
  if h : Module.InFeat S mod then some ⟨mod, h⟩ else none

/-- The complete module has no host imports or linear resources and exports
only functions. Local tag declarations are governed separately by `features`.
This checks shape, not validity of any function export or start index. -/
def FunctionalCore.closedShape (mod : Wasm.Module) : Bool :=
  mod.imports.isEmpty && mod.memories.isEmpty && mod.tables.isEmpty && mod.globals.isEmpty &&
    mod.elems.isEmpty && mod.data.isEmpty && mod.exports.all fun entry =>
      match entry.index with | .func _ => true | _ => false

def FunctionalCore.accepts (gc : GCMode) (exceptions : ExceptionMode) (mod : Wasm.Module) : Prop :=
  Module.InFeat (features gc exceptions) mod ∧ closedShape mod = true

instance (gc : GCMode) (exceptions : ExceptionMode) (mod : Wasm.Module) :
    Decidable (FunctionalCore.accepts gc exceptions mod) := inferInstanceAs (Decidable (_ ∧ _ = true))

instance (gc : GCMode) (exceptions : ExceptionMode) : HasSyntax (FunctionalCore gc exceptions) := ⟨
  { val : ValType // ValType.InFeat (FunctionalCore.features gc exceptions) val },
  { instr : Instr // Instr.InFeat (FunctionalCore.features gc exceptions) instr },
  { body : Expr // Instr.insInFeatB (FunctionalCore.features gc exceptions) body = true },
  { fn : Func // Func.inFeatB (FunctionalCore.features gc exceptions) fn = true },
  { mod : Wasm.Module // FunctionalCore.accepts gc exceptions mod }⟩

instance (gc : GCMode) (exceptions : ExceptionMode) : HasTyping (FunctionalCore gc exceptions) where
  Context := Validation.Context
  FuncType := Validation.DefType
  Interface := Validation.CModuleType
  funcOk ctx fn sig := Validation.FuncOk ctx fn.val sig
  moduleOk mod iface := Validation.ModuleOk mod.val iface

def FunctionalCore.check? (gc : GCMode) (exceptions : ExceptionMode) (mod : Wasm.Module) :
    Option (Module (FunctionalCore gc exceptions)) :=
  if h : accepts gc exceptions mod then some ⟨mod, h⟩ else none

abbrev Strict.accepts := FunctionalCore.accepts .immutable .disabled
abbrev Strict.check? := FunctionalCore.check? .immutable .disabled

def Strict.parts (mod : Module Strict) : ModuleParts Func := mod.val.split

end Silmaril.Wasm.Profiles
