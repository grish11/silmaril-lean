module

import Silmaril.Formats.Dasl.SExp.Bridge.Thms

namespace Silmaril.Formats.Dasl.SExp.Bridge.Examples

open Silmaril.Semantics.Naming

private def leaf : Formats.SExp String := .atom "x"
private def expr : Formats.SExp String := .list 1 fun _ => leaf
private def child : Named Nat := Proper.write Payload.utf8 inlineAll leaf
private def first : Named Nat := Proper.write Payload.utf8 (linkAll fun _ _ => 10) expr
private def second : Named Nat := Proper.write Payload.utf8 (linkAll fun _ _ => 11) expr
private def dangling : Named Nat := Proper.write Payload.utf8 (linkAll fun _ _ => 12) expr

private def lookup : Nat → Option (Shallow Nat)
  | 0 => some first.embed.shallow
  | 1 => some second.embed.shallow
  | 2 => some dangling.embed.shallow
  | 10 | 11 => some child.embed.shallow
  | _ => none

private def store : Store Nat := ⟨graph lookup, fun _ _ => False⟩

private theorem bound : store.Binding :=
  ⟨fun {_ _ _} left right => Option.some.inj (left.symm.trans right),
    fun {_ _ _} impossible _ => impossible.elim⟩

private theorem firstFull : FullNames store 0 first :=
  ⟨_, rfl, .list fun _ => .obj (show store.objects 10 child.embed.shallow from rfl) (.dict fun _ => .bytes _)⟩

private theorem secondFull : FullNames store 1 second :=
  ⟨_, rfl, .list fun _ => .obj (show store.objects 11 child.embed.shallow from rfl) (.dict fun _ => .bytes _)⟩

private theorem firstRead : Proper.read Payload.utf8 first.embed = some expr := by
  rw [first, Proper.write_embed]
  exact Proper.read_write _ _ _

private theorem secondRead : Proper.read Payload.utf8 second.embed = some expr := by
  rw [second, Proper.write_embed]
  exact Proper.read_write _ _ _

private theorem aliases : (rootPER store bound (Proper.read Payload.utf8)).rel 0 1 :=
  ⟨expr, ⟨first, firstFull, firstRead⟩, ⟨second, secondFull, secondRead⟩⟩

example : (namedPER (Proper.read Payload.utf8)).rel first second := ⟨expr, firstRead, secondRead⟩

example : ∃ item, Observes store (Proper.read Payload.utf8) 0 item ∧ Observes store (Proper.read Payload.utf8) 1 item :=
  (observed_rel bound (Proper.read Payload.utf8) (fun {_ _ _} step hit => Proper.read_mono _ step hit)
    ⟨0, _, firstFull⟩ ⟨1, _, secondFull⟩).1 aliases

example : ∃ normal : Named Nat,
    normalize (Proper.read Payload.utf8) (Proper.write Payload.utf8 inlineAll) first.embed = some normal ∧
    normalize (Proper.read Payload.utf8) (Proper.write Payload.utf8 inlineAll) second.embed = some normal :=
  (root_rel_normalize bound (Proper.read Payload.utf8) (Proper.codec Payload.utf8 inlineAll)
    firstFull secondFull).1 aliases

example : ¬ (presentationPER (Proper.read Payload.utf8)).Dom dangling.embed.shallow.embed := by
  rw [presentation_dom, show Proper.read Payload.utf8 dangling.embed.shallow.embed = none from rfl]
  simp

example : SExpDasl.symbols.parseAbstract? (Proper.read Payload.utf8) first.embed =
    some (SExpDasl.symbols.intoAbstract expr) := by
  simp [Encode.TotalCodec.parseAbstract?, firstRead]

private def dotted : SExp2 ByteArray := .cons (.atom ByteArray.empty) (.atom ByteArray.empty)
private def writtenDotted : Partial Nat := Dotted.write .dict Payload.bytes (linkAll fun _ _ => 10) dotted

example : (Dotted.readTree .dict Payload.bytes writtenDotted).map (SExp2.equivTreeOption ByteArray).symm =
    some dotted := (Dotted.tree_recover _ _ _).trans (Dotted.read_write _ _ _ _)

example : Dotted.properAbstract? .dict Payload.bytes Payload.bytes.asValue writtenDotted = none :=
  Dotted.proper_abstract_rejects_improper _ _ _ (Dotted.read_write _ _ _ _) (by decide)

end Silmaril.Formats.Dasl.SExp.Bridge.Examples
