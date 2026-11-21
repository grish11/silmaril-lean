module

public import Silmaril.Wasm.Profiles.Injections.Defs
import Silmaril.Proofs.Wasm.Profiles.InjectionDomain

public section

namespace Silmaril.Wasm.Profiles

namespace PartialInjection

variable {Source Middle Target Last : Type}

@[ext] theorem ext {left right : PartialInjection Source Target} (run_eq : left.run = right.run) : left = right := by
  cases left; cases right; cases run_eq; rfl

@[simp] theorem id_comp (arrow : PartialInjection Source Target) : (id Target).comp arrow = arrow :=
  ext (funext fun source => by
    change (arrow.run source).bind some = arrow.run source
    cases arrow.run source <;> rfl)

@[simp] theorem comp_id (arrow : PartialInjection Source Target) : arrow.comp (id Source) = arrow := rfl

theorem comp_assoc (third : PartialInjection Target Last) (second : PartialInjection Middle Target)
    (first : PartialInjection Source Middle) :
    (third.comp second).comp first = third.comp (second.comp first) :=
  ext (funext fun source => (Option.bind_assoc (first.run source) second.run third.run).symm)

@[simp] theorem ofEmbedding_comp (first : Source ↪ Middle) (second : Middle ↪ Target) :
    (ofEmbedding second).comp (ofEmbedding first) = ofEmbedding (first.trans second) := rfl

theorem onDomain_spec (arrow : PartialInjection Source Target) (source : arrow.Domain) :
    arrow.run source.val = some (arrow.onDomain source) := (Option.some_get source.property).symm

end PartialInjection

namespace Injections

theorem wasm1_via_lime : wasm1ToLime.trans limeToWasm2 = wasm1ToWasm2 := rfl

theorem wasm1_core_via_lime (source : Module Wasm1) :
    limeToWasm3 (wasm1ToLime source) = wasm1ToWasm3 source := V1.Module.toLime_toCore source

theorem lime_core_via_wasm2 : (wasm2ToWasm3.comp (PartialInjection.ofEmbedding limeToWasm2)) =
    PartialInjection.ofEmbedding limeToWasm3 :=
  PartialInjection.ext (funext Lime1.Module.toV2_toCore)

theorem wasm1_core_via_wasm2 : (wasm2ToWasm3.comp (PartialInjection.ofEmbedding wasm1ToWasm2)) =
    PartialInjection.ofEmbedding wasm1ToWasm3 :=
  PartialInjection.ext (funext V1.Module.toV2_toCore)

theorem wasm1_function_core_via_wasm2 :
    wasm2ToWasm3Function.comp (PartialInjection.ofEmbedding wasm1ToWasm2Function) =
      PartialInjection.ofEmbedding wasm1ToWasm3Function := by
  apply PartialInjection.ext; funext source
  exact (Lime1.Func.toV2_toCore source.toLime).trans (congrArg some (V1.Func.toLime_toCore source))

theorem lime_function_core_via_wasm2 :
    wasm2ToWasm3Function.comp (PartialInjection.ofEmbedding limeToWasm2Function) =
      PartialInjection.ofEmbedding limeToWasm3Function :=
  PartialInjection.ext (funext Lime1.Func.toV2_toCore)

theorem wasm2_binary_via_ast (source : Module Wasm2) :
    wasm2ToWasm3Binary.run source = (wasm2ToWasm3.run source).map V2.Module.binaryRetype := rfl

theorem wasm1_fx_via_wasm2 : wasm2ToFX.comp (PartialInjection.ofEmbedding wasm1ToWasm2) =
    PartialInjection.ofEmbedding (wasm1ToWasm3.trans wasm3ToFX) := by
  rw [wasm2ToFX, PartialInjection.comp_assoc, wasm1_core_via_wasm2]
  rfl

theorem wasm2Function_defined {context : V2.Validation.Context} {source : Function Wasm2} {sig : V2.FuncType}
    (checked : V2.Validation.FuncOk context source sig) :
    ∃ core, wasm2ToWasm3Function.run source = some core := Proofs.Profiles.InjectionDomain.funcDefined checked

theorem wasm2Module_defined {ports : HasTyping.Interface Wasm2} (source : CheckedModule Wasm2 ports) :
    ∃ core, wasm2ToWasm3.run source.val = some core := Proofs.Profiles.InjectionDomain.moduleDefined source.property

theorem wasm2Module_isSome {ports : HasTyping.Interface Wasm2} (source : CheckedModule Wasm2 ports) :
    (wasm2ToWasm3.run source.val).isSome := Option.isSome_iff_exists.mpr (wasm2Module_defined source)

/-- Unlike the raw injection, the map on natively checked V2 modules is total. -/
def checkedWasm2ToWasm3 {ports : HasTyping.Interface Wasm2} (source : CheckedModule Wasm2 ports) :
    CheckedModule Wasm3 (wasm2Interface ports) :=
  let defined := wasm2Module_isSome source
  ⟨wasm2ToWasm3.onDomain ⟨source.val, defined⟩,
    V2.Validation.ModuleOk.toCore (Option.some_get defined).symm source.property⟩

theorem checkedWasm2ToWasm3_erasure {ports : HasTyping.Interface Wasm2} (source : CheckedModule Wasm2 ports) :
    wasm2ToWasm3.run source.val = some (checkedWasm2ToWasm3 source).val :=
  wasm2ToWasm3.onDomain_spec ⟨source.val, wasm2Module_isSome source⟩

/-- A total embedding at each retained native V2 import/export interface. -/
def checkedWasm2ToWasm3Embedding (ports : HasTyping.Interface Wasm2) :
    CheckedModule Wasm2 ports ↪ CheckedModule Wasm3 (wasm2Interface ports) where
  toFun := checkedWasm2ToWasm3
  inj' := by
    intro left right eq
    exact Subtype.ext (wasm2ToWasm3.injectiveOnSuccess (checkedWasm2ToWasm3_erasure left)
      ((checkedWasm2ToWasm3_erasure right).trans (congrArg (fun mod => some mod.val) eq.symm)))

theorem checkedWasm2ToWasm3_lift {ports : HasTyping.Interface Wasm2} (source : CheckedModule Wasm2 ports) :
    ∃ typed : TypedModule Wasm3 (wasm2Interface ports),
      HasIntrinsic.eraseModule typed = (checkedWasm2ToWasm3 source).val :=
  HasIntrinsic.moduleLift (checkedWasm2ToWasm3 source).property

theorem checkedWasm1_via_lime (source : CheckedModule Wasm1 ()) :
    validLimeToWasm3 (checkedWasm1ToLime source) = validWasm1ToWasm3 source :=
  Subtype.ext (wasm1_core_via_lime source.val)

theorem checkedWasm1_via_wasm2 (source : CheckedModule Wasm1 ())
    {ports : HasTyping.Interface Wasm2} (checked : HasTyping.moduleOk (wasm1ToWasm2 source.val) ports) :
    (checkedWasm2ToWasm3 (ports := ports) ⟨wasm1ToWasm2 source.val, checked⟩).val =
      (validWasm1ToWasm3 source).val :=
  Option.some.inj ((checkedWasm2ToWasm3_erasure ⟨_, checked⟩).symm.trans (V1.Module.toV2_toCore source.val))

theorem checkedLime_via_wasm2 (source : CheckedModule Lime ())
    {ports : HasTyping.Interface Wasm2} (checked : HasTyping.moduleOk (limeToWasm2 source.val) ports) :
    (checkedWasm2ToWasm3 (ports := ports) ⟨limeToWasm2 source.val, checked⟩).val =
      (validLimeToWasm3 source).val :=
  Option.some.inj ((checkedWasm2ToWasm3_erasure ⟨_, checked⟩).symm.trans (Lime1.Module.toV2_toCore source.val))

end Injections

end Silmaril.Wasm.Profiles
