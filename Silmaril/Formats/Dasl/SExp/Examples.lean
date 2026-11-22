module

import Silmaril.Formats.Dasl.SExp.Thms

namespace Silmaril.Formats.Dasl.SExp.Examples

open Silmaril.Semantics.Naming

private def form : Formats.SExp String :=
  Formats.SExp.ofList [.atom "x", Formats.SExp.ofList [.atom "y"]]

private def layoutName (path : Path) (_ : Formats.SExp String) : Nat :=
  match path with
  | [0] => 10
  | [1] => 11
  | _ => 12

private def allLinked : Named Nat := Proper.write Payload.utf8 (linkAll layoutName) form
private def listsLinked : Named Nat := Proper.write Payload.utf8 (properNonAtoms layoutName) form
private def inlineForm : Named Nat := Proper.write Payload.utf8 inlineAll form

private def topLinks : Shallow Nat → Option (List (Option (Link Nat)))
  | .list _ items => some (List.ofFn fun index => match items index with | .ref link => some link | _ => none)
  | _ => none

example : topLinks allLinked.embed.shallow = some [some (.obj 10), some (.obj 11)] := rfl
example : topLinks listsLinked.embed.shallow = some [none, some (.obj 11)] := rfl
example : topLinks inlineForm.embed.shallow = some [none, none] := rfl

example : normalize (Proper.read Payload.utf8) (Proper.write Payload.utf8 (linkAll layoutName))
    listsLinked = some allLinked := normalize_write (Proper.codec Payload.utf8 (properNonAtoms layoutName))
      (Proper.codec Payload.utf8 (linkAll layoutName)) form

example : Proper.read Payload.utf8 allLinked.embed.shallow.embed = none := rfl

private def atomTree : Named Nat := Proper.write Payload.utf8 inlineAll (.atom "x")
private def aliasForm : Formats.SExp String := .list 1 fun _ => .atom "x"
private def linked : Named Nat := Proper.write Payload.utf8 (linkAll fun _ _ => 11) aliasForm
private def inlined : Named Nat := Proper.write Payload.utf8 inlineAll aliasForm

private def lookup : Nat → Option (Shallow Nat)
  | 0 => some linked.embed.shallow
  | 1 => some inlined.embed.shallow
  | 11 => some atomTree.embed.shallow
  | _ => none

private def fixture : Store Nat where
  objects := graph lookup
  blobs := fun _ _ => False

private theorem fixture_binding : fixture.Binding := by
  constructor
  · intro _ _ _ first second
    exact Option.some.inj (first.symm.trans second)
  · intro _ _ _ impossible _
    exact impossible.elim

private theorem linkedFull : FullNames fixture 0 linked :=
  ⟨linked.embed.shallow, rfl, .list fun _ => .obj (show fixture.objects 11 atomTree.embed.shallow from rfl)
    (.dict fun _ => .bytes _)⟩

private theorem inlineFull : FullNames fixture 1 inlined :=
  ⟨inlined.embed.shallow, rfl, .list fun _ => .dict fun _ => .bytes _⟩

private theorem linkedRead : Proper.read Payload.utf8 linked.embed = some aliasForm := by
  rw [linked, Proper.write_embed]
  exact Proper.read_write _ _ _

private theorem inlineRead : Proper.read Payload.utf8 inlined.embed = some aliasForm := by
  rw [inlined, Proper.write_embed]
  exact Proper.read_write _ _ _

/-- Two names and two different shallow trees, but the same decoded syntax. -/
example : Aliases fixture (Proper.read Payload.utf8) 0 1 :=
  ⟨aliasForm, ⟨linked, linkedFull, linkedRead⟩, ⟨inlined, inlineFull, inlineRead⟩⟩

example : Observes fixture (Proper.read Payload.utf8) 0 aliasForm :=
  (observations_agree fixture_binding (Proper.read Payload.utf8) (fun {_ _ _} step hit => Proper.read_mono _ step hit)
    linkedFull).2 linkedRead

/-- A dotted-tail atom is a child that may be linked in either layout. -/
private def dotted : SExp2 ByteArray :=
  .cons (.atom ⟨#[0x01, 0x71, 0x1e, 0x20]⟩) (.cons .nil (.atom ⟨#[0x55]⟩))

private def dottedName (path : Path) (_ : SExp2 ByteArray) : Nat := path.length

private def dottedDict : Partial Nat := Dotted.write .dict Payload.bytes (linkAll dottedName) dotted
private def dottedArray : Partial Nat := Dotted.write .array Payload.bytes inlineAll dotted

example : Dotted.transcode .dict .array Payload.bytes inlineAll dottedDict = some dottedArray :=
  Dotted.transcode_write .dict .array Payload.bytes (linkAll dottedName) inlineAll dotted

example : Dotted.transcode .array .dict Payload.bytes (linkAll dottedName) dottedArray = some dottedDict :=
  Dotted.transcode_write .array .dict Payload.bytes inlineAll (linkAll dottedName) dotted

example : Dotted.read .dict Payload.bytes (Tree.ref (Link.blob (7 : Nat)) : Partial Nat) = none := rfl
example : Proper.read Payload.utf8 (Tree.obj 11 atomTree : Named Nat) = none := rfl

end Silmaril.Formats.Dasl.SExp.Examples
