module

import Silmaril.Formats.Dasl.Arena.Thms
import Silmaril.Formats.Dasl.Wire.Canonical.Thms

namespace Silmaril.Formats.Dasl.Arena.Examples

open Silmaril.Semantics.Arena

private def data : Dense 5 Nat String := ⟨#[none, some ⟨none, none⟩, some ⟨some 9, none⟩,
  some ⟨none, some "unassigned"⟩, some ⟨some 7, some "resident"⟩], rfl⟩

private def taggedText : Codec Nat String (Shallow Nat)
  | some 7 => Encode.text.partial
  | _ => ⟨fun _ => none, fun _ => none, fun _ _ impossible => by cases impossible⟩

example : (Codec.encode taggedText).strictDense data = .error ⟨3, by decide⟩ := rfl

example : ((Codec.encode taggedText).discardDense data).val =
    #[none, some ⟨none, none⟩, some ⟨some 9, none⟩, some ⟨none, none⟩, some ⟨some 7, some (.string "resident")⟩] := rfl

example : ((Codec.lift (Name := Nat) (Target := Shallow Nat) Encode.text.partial).encode.strictDense data).isOk =
    true := rfl

private def canonicalText : Codec Wire.Cid String ByteArray :=
  (Codec.lift Encode.text.partial).then (Codec.lift Wire.canonicalCodec)

example (bytes : ByteArray) (encoded : canonicalText.encode none "arena" = some bytes) :
    canonicalText.decode none bytes = some "arena" := (canonicalText none).recovers encoded

end Silmaril.Formats.Dasl.Arena.Examples
