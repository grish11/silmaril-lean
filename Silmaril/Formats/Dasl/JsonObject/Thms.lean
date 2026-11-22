module

public import Silmaril.Formats.Dasl.JsonObject.Defs
import Silmaril.Proofs.Formats.Dasl.JsonObject

public section

namespace Silmaril.Formats.Dasl.JsonObject

open Semantics.Naming

@[simp] theorem decode_encode (object : Object) : decode? (encode object) = some object :=
  Proofs.Formats.Dasl.JsonObject.decode_encode object

theorem encode_injective : Function.Injective encode :=
  fun _ _ same => Option.some.inj (by simpa only [decode_encode] using congrArg decode? same)

theorem encoded_eq_iff {left right : Object} : encode left = encode right ↔ left = right :=
  ⟨fun same => encode_injective same, congrArg encode⟩

/-- A total, coherent *fixed* relation gives exactly one name per supported object.
It need not be binding in the other direction. -/
theorem exactly_one_name {Name : Type} {observe : Relation Name (List UInt8)}
    (coherent : UniqueNames observe) (total : ∀ bytes, ∃ name, observe name bytes)
    (object : Object) : ∃! name, names observe name object := by
  obtain ⟨name, found⟩ := total (encode object)
  exact ⟨name, found, fun _ other => coherent other found⟩

/-- Distinct objects cannot share a name if the observed byte relation is also binding. -/
theorem names_binding {Name : Type} {observe : Relation Name (List UInt8)}
    (bound : Binding observe) : Binding (names observe) :=
  fun _ _ _ first second => encode_injective (bound first second)

end Silmaril.Formats.Dasl.JsonObject
