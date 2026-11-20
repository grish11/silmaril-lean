module

public import Silmaril.Wasm.Validation.Generic.Signature.Defs
public import Silmaril.Wasm.Validation.Generic.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Validation.Generic.Signature

public section

namespace Silmaril.Wasm.Generic.Signature

open Validation

variable {T U V Out : Type} {B : Func T → Type} {C : Func U → Type} {D : Func V → Type}

@[simp] theorem Func.map_id (sig : Func T) : sig.map id = sig := by cases sig; simp [map]

theorem Func.map_comp (f : T → U) (g : U → V) (sig : Func T) :
    (sig.map f).map g = sig.map (g ∘ f) := by cases sig; simp [map, List.map_map, Function.comp_def]

theorem Module.map_id (mod : Module B) :
    mod.map id (fun {sig} body => cast (congrArg B sig.map_id.symm) body) = mod :=
  Proofs.Wasm.Validation.Generic.Signature.module_id Func.map_id mod

theorem Module.map_comp (f : T → U) (g : U → V) (first : ∀ {sig}, B sig → C (sig.map f))
    (second : ∀ {sig}, C sig → D (sig.map g)) (mod : Module B) :
    (mod.map f first).map g second = mod.map (g ∘ f)
      (fun {sig} body => cast (congrArg D (sig.map_comp f g)) (second (first body))) :=
  Proofs.Wasm.Validation.Generic.Signature.module_comp f g first second (Func.map_comp f g) mod

@[simp] theorem Module.signatureAt_map (f : T → U) (lift : ∀ {sig}, B sig → C (sig.map f))
    (mod : Module B) (index : FuncIdx) : (mod.map f lift).signatureAt? index =
      (mod.signatureAt? index).map (Func.map f) := by
  simp [signatureAt?, map, Option.map_map, Function.comp_def, Slot.map]

theorem Func.encode_map (f : T → U) (source : Encoding T) (target : Encoding U)
    (args : ∀ type, target.arg (f type) = source.arg type)
    (results : ∀ type, target.result (f type) = source.result type) (sig : Func T) :
    (sig.map f).encode? target = sig.encode? source := by
  simp [encode?, map, Function.comp_def, args, results]

/-- Retyping commutes with specialization (including failures) provided the
external encodings and emitted payload agree, not merely their result types. -/
theorem Module.specialize_map (f : T → U) (lift : ∀ {sig}, B sig → C (sig.map f))
    (source : Encoding T) (target : Encoding U)
    (sourceEmit : ∀ {sig}, TypeIdx → FuncType → B sig → Option (List ValType × Out))
    (targetEmit : ∀ {sig}, TypeIdx → FuncType → C sig → Option (List ValType × Out))
    (types : ∀ sig : Func T, (sig.map f).encode? target = sig.encode? source)
    (code : ∀ {sig} (body : B sig) index type, targetEmit index type (lift body) = sourceEmit index type body)
    (mod : Module B) : (mod.map f lift).specialize? target targetEmit = mod.specialize? source sourceEmit := by
  unfold specialize? map
  rw [Proofs.Wasm.Validation.Generic.Signature.encode_slots_map f lift source target sourceEmit targetEmit types code]

/-- The executable validator can certify specialized code outside the computable
intrinsic reifier's profile. The resulting intrinsic lift is existential. -/
theorem checkedLift {raw : RawModule Wasm.Func} {interface : CModuleType}
    (checked : validate? raw.toCore = some interface) :
    ∃ typed : Typed.Module (Typed.Function Intrinsic.Body) interface,
      typed.forget Typed.Function.erase = raw := by
  obtain ⟨typed, erased⟩ := Typed.Module.lift_erase (validate?_sound checked)
  exact ⟨typed, RawModule.toCore_injective ((Typed.Module.forget_toCore typed).trans erased)⟩

end Silmaril.Wasm.Generic.Signature
