module

public import Silmaril.Wasm.Validation.Generic.Signature.Defs

public section

namespace Silmaril.Proofs.Wasm.Validation.Generic.Signature

open Silmaril.Wasm Silmaril.Wasm.Generic.Signature

variable {T U V Out : Type} {B : Func T → Type} {C : Func U → Type} {D : Func V → Type}

theorem slot_cast {sig target : Func T} (same : sig = target) (body : B sig) :
    Slot.mk target (cast (congrArg B same) body) = Slot.mk sig body := by
  cases same
  rfl

theorem module_id (law : ∀ sig : Func T, sig.map id = sig) (mod : Module B) :
    mod.map id (fun {sig} body => cast (congrArg B (law sig).symm) body) = mod := by
  have same : Slot.map (B := B) (C := B) id (fun {sig} body => cast (congrArg B (law sig).symm) body) = id := by
    funext slot
    exact slot_cast (law slot.sig).symm slot.body
  cases mod
  simp [Module.map, same]

theorem module_comp (f : T → U) (g : U → V) (first : ∀ {sig}, B sig → C (sig.map f))
    (second : ∀ {sig}, C sig → D (sig.map g))
    (law : ∀ sig : Func T, (sig.map f).map g = sig.map (g ∘ f)) (mod : Module B) :
    (mod.map f first).map g second = mod.map (g ∘ f)
      (fun {sig} body => cast (congrArg D (law sig)) (second (first body))) := by
  have same : Slot.map g second ∘ Slot.map f first = Slot.map (g ∘ f)
      (fun {sig} body => cast (congrArg D (law sig)) (second (first body))) := by
    funext slot
    exact (slot_cast (law slot.sig) (second (first slot.body))).symm
  cases mod
  simp [Module.map, List.map_map, same]

theorem encode_slots_map (f : T → U) (lift : ∀ {sig}, B sig → C (sig.map f))
    (source : Encoding T) (target : Encoding U)
    (sourceEmit : ∀ {sig}, TypeIdx → FuncType → B sig → Option (List ValType × Out))
    (targetEmit : ∀ {sig}, TypeIdx → FuncType → C sig → Option (List ValType × Out))
    (types : ∀ sig : Func T, (sig.map f).encode? target = sig.encode? source)
    (code : ∀ {sig} (body : B sig) index type, targetEmit index type (lift body) = sourceEmit index type body)
    (index : Nat) (slots : List (Slot B)) :
    encodeSlots? target targetEmit index (slots.map (Slot.map (B := B) (C := C) f lift)) =
      encodeSlots? source sourceEmit index slots := by
  induction slots generalizing index with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, encodeSlots?, Slot.map, types, code, ih]

end Silmaril.Proofs.Wasm.Validation.Generic.Signature
