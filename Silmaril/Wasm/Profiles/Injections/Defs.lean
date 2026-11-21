module

public import Silmaril.Wasm.Profiles.Defs
public import Silmaril.Wasm.Versions.Thms

/-! # Version injections on the native profile ASTs

A partial injection is injective on successful translations, not on failed
ones. The maps here select source-AST translations, not validators, binary
rewriters, or a choice of operational semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Profiles

structure PartialInjection (Source Target : Type) where
  run : Source → Option Target
  injectiveOnSuccess : ∀ {left right image}, run left = some image → run right = some image → left = right

namespace PartialInjection

variable {Source Middle Target : Type}

def ofEmbedding (arrow : Source ↪ Target) : PartialInjection Source Target where
  run source := some (arrow source)
  injectiveOnSuccess left right := arrow.injective (Option.some.inj (left.trans right.symm))

def id (Source : Type) : PartialInjection Source Source := ofEmbedding (Function.Embedding.refl Source)

def comp (second : PartialInjection Middle Target) (first : PartialInjection Source Middle) :
    PartialInjection Source Target where
  run source := (first.run source).bind second.run
  injectiveOnSuccess left right := by
    obtain ⟨_, il, ol⟩ := Option.bind_eq_some_iff.mp left
    obtain ⟨_, ir, or⟩ := Option.bind_eq_some_iff.mp right
    exact first.injectiveOnSuccess il ((second.injectiveOnSuccess ol or).symm ▸ ir)

def Domain (arrow : PartialInjection Source Target) := { source // (arrow.run source).isSome }

/-- An ordinary embedding of the computably defined source domain. -/
def onDomain (arrow : PartialInjection Source Target) : arrow.Domain ↪ Target where
  toFun source := (arrow.run source.val).get source.property
  inj' := by
    intro left right eq
    exact Subtype.ext (arrow.injectiveOnSuccess (Option.some_get _).symm ((Option.some_get _).symm.trans (congrArg some eq.symm)))

end PartialInjection

abbrev ModuleInjection (A B : Type) [HasSyntax A] [HasSyntax B] := PartialInjection (Module A) (Module B)
abbrev FunctionInjection (A B : Type) [HasSyntax A] [HasSyntax B] := PartialInjection (Function A) (Function B)

namespace Injections

def wasm1ToLime : Module Wasm1 ↪ Module Lime := ⟨V1.Module.toLime, V1.Module.toLime_injective⟩
def limeToWasm2 : Module Lime ↪ Module Wasm2 := ⟨Lime1.Module.toV2, Lime1.Module.toV2_injective⟩
def wasm1ToWasm2 : Module Wasm1 ↪ Module Wasm2 := ⟨V1.Module.toV2, V1.Module.toV2_injective⟩
def wasm1ToWasm3 : Module Wasm1 ↪ Module Wasm3 := ⟨V1.Module.toCore, V1.Module.toCore_injective⟩
def limeToWasm3 : Module Lime ↪ Module Wasm3 := ⟨Lime1.Module.toCore, Lime1.Module.toCore_injective⟩

/-- Raw V2 admits conversion triples with no corresponding Core instruction. -/
def wasm2ToWasm3 : ModuleInjection Wasm2 Wasm3 := ⟨V2.Module.toCore, V2.Module.toCore_injective⟩

/-- Separate binary-faithful route: the legacy function-index element forms
are retagged non-nullable, not translated by the ordinary syntax injection. -/
def wasm2ToWasm3Binary : ModuleInjection Wasm2 Wasm3 :=
  ⟨V2.Module.toCoreBinary, V2.Module.toCoreBinary_injective⟩

/-- FX still loads a Core AST; its extra host-code bindings are separate. -/
def wasm3ToFX : Module Wasm3 ↪ Module FX := Function.Embedding.refl _

def wasm3ToFXUnbound (HostCode : Type) : Module Wasm3 ↪ FX.WithBindings HostCode :=
  ⟨FX.WithBindings.ofCore, fun {_ _} eq => congrArg FX.WithBindings.core eq⟩

def wasm2ToFX : ModuleInjection Wasm2 FX := (PartialInjection.ofEmbedding wasm3ToFX).comp wasm2ToWasm3

def wasm1ToLimeFunction : Function Wasm1 ↪ Function Lime := ⟨V1.Func.toLime, V1.Func.toLime_injective⟩
def limeToWasm2Function : Function Lime ↪ Function Wasm2 := ⟨Lime1.Func.toV2, Lime1.Func.toV2_injective⟩
def wasm1ToWasm2Function : Function Wasm1 ↪ Function Wasm2 := wasm1ToLimeFunction.trans limeToWasm2Function
def wasm1ToWasm3Function : Function Wasm1 ↪ Function Wasm3 :=
  ⟨V1.Func.toCore, fun {_ _} eq => Option.some.inj (by simpa only [V1.Func.ofCore?_toCore] using congrArg V1.Func.ofCore? eq)⟩
def limeToWasm3Function : Function Lime ↪ Function Wasm3 := ⟨Lime1.Func.toCore, Lime1.Func.toCore_injective⟩
def wasm2ToWasm3Function : FunctionInjection Wasm2 Wasm3 := ⟨V2.Func.toCore, V2.Func.toCore_injective⟩

def wasm3ToFXInstruction : Instruction Wasm3 ↪ Instruction FX :=
  ⟨Models.FX.InstrFX.core, fun {_ _} eq => Models.FX.InstrFX.core.inj eq⟩

def wasm2Interface (ports : HasTyping.Interface Wasm2) : HasTyping.Interface Wasm3 :=
  ⟨ports.1.map V2.ExternType.toCore, ports.2.map V2.ExternType.toCore⟩

def checkedWasm1ToLime (source : CheckedModule Wasm1 ()) : CheckedModule Lime () :=
  ⟨wasm1ToLime source.val, V1.Validation.ModuleValid.toLime source.property⟩

def validWasm1ToWasm2 (source : CheckedModule Wasm1 ())
    (offsets : Lime1.Validation.Module.SegmentOffsetsImported (wasm1ToLime source.val)) : ValidModule Wasm2 :=
  ⟨wasm1ToWasm2 source.val, by
    obtain ⟨imports, exports, checked⟩ := V1.Validation.ModuleValid.toV2 source.property offsets
    exact ⟨(imports, exports), checked⟩⟩

def validLimeToWasm2 (source : CheckedModule Lime ())
    (consts : Lime1.Validation.Module.NoExtendedConst source.val)
    (offsets : Lime1.Validation.Module.SegmentOffsetsImported source.val) : ValidModule Wasm2 :=
  ⟨limeToWasm2 source.val, by
    obtain ⟨imports, exports, checked⟩ := Lime1.Validation.ModuleValid.toV2 source.property consts offsets
    exact ⟨(imports, exports), checked⟩⟩

def validWasm1ToWasm3 (source : CheckedModule Wasm1 ()) : ValidModule Wasm3 :=
  ⟨wasm1ToWasm3 source.val, V1.Validation.ModuleValid.toCore source.property⟩

def validLimeToWasm3 (source : CheckedModule Lime ()) : ValidModule Wasm3 :=
  ⟨limeToWasm3 source.val, Lime1.Validation.ModuleValid.toCore source.property⟩

end Injections

end Silmaril.Wasm.Profiles
