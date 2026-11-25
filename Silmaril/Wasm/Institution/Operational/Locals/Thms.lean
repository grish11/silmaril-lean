module

public import Silmaril.Wasm.Institution.Operational.Locals.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Locals.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

theorem fact {a b : State} (h : RuleInstance ⟨[], (a, b)⟩) : Edge a b :=
  Derives.apply (R := presentation.rules) (r := ⟨[], (a, b)⟩) h (fun _ h => nomatch h)

theorem context {a b : State} (step : Edge a b) (saved : List Value) (tail : List Op) :
    Edge ⟨a.locals, values saved ++ a.code ++ tail⟩ ⟨b.locals, values saved ++ b.code ++ tail⟩ :=
  Derives.apply (R := presentation.rules) (r := ⟨[(a, b)], _, _⟩) (.context a b saved tail)
    (fun _ h => (List.mem_singleton.mp h).symm ▸ step)

theorem closed {a b : State} {types result : List NumType} (guard : Admitted types result a)
    (edge : Edge a b) : Admitted types result b := Proofs.closed guard edge

theorem run_closed {a b : State} {types result : List NumType} (guard : Admitted types result a)
    (run : Runs a b) : Admitted types result b := by
  induction run with
  | refl => exact guard
  | tail _ h ih => exact closed ih h

namespace Codec
variable {A : Type} (C : Codec A)

@[simp] theorem decode_encode (code : List Op) : C.decode (C.encode code) = code := by
  simp [decode, encode, List.filterMap_map, C.read_emit]

@[simp] theorem supports_nil : C.Supported [] := fun _ h => nomatch h

@[simp] theorem supports_cons {a : A} {code : List A} :
    C.Supported (a :: code) ↔ (C.read a).isSome ∧ C.Supported code := List.forall_mem_cons

@[simp] theorem supports_append {a b : List A} :
    C.Supported (a ++ b) ↔ C.Supported a ∧ C.Supported b := List.forall_mem_append

@[simp] theorem encode_append (a b : List Op) : C.encode (a ++ b) = C.encode a ++ C.encode b :=
  List.map_append

theorem supports_encode (code : List Op) : C.Supported (C.encode code) := by
  intro a ha
  obtain ⟨op, _, rfl⟩ := List.mem_map.mp ha
  simp [C.read_emit]

@[simp] theorem decode_append (a b : List A) : C.decode (a ++ b) = C.decode a ++ C.decode b :=
  List.filterMap_append

theorem encode_decode {code : List A} (h : C.Supported code) : C.encode (C.decode code) = code := by
  induction code with
  | nil => rfl
  | cons a code ih =>
    obtain ⟨head, tail⟩ := List.forall_mem_cons.mp h
    cases found : C.read a with
    | none => simp [found] at head
    | some op => simpa [encode, decode, found, C.emit_read found] using congrArg (List.cons a) (ih tail)

end Codec
end Silmaril.Wasm.Institution.Operational.Locals
