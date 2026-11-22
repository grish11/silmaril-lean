module

import Silmaril.Formats.Dasl.Comparison.Conservative.Thms
import Silmaril.Formats.Dasl.Presentation.Thms

namespace Silmaril.Formats.Dasl

private def blobReader (payload : Option ByteArray) : Reader Unit where
  object? := fun _ => some (.ref (.blob ()))
  blob? := fun _ => payload

private def missing := blobReader none
private def available := blobReader (some ByteArray.empty)
private def namedBlob : Named Unit := .blob () ByteArray.empty
private def payload : Encode.Blob := ⟨ByteArray.empty⟩

example : ∃ tree : Named.Valid available.store,
    tree.val.erase = (Encode.blob.intoAbstract payload).val ∧ tree.val.embed.shallow = .ref (.blob ()) :=
  Named.exists_valid_lift_iff.mpr ⟨available.binding, CanName.blob rfl⟩

example : Encode.blob.fromAbstract? (Encode.blob.intoAbstract payload) = some payload ∧
    ¬ ∃ tree : Named Unit, tree.erase = (Encode.blob.intoAbstract payload).val ∧ tree.Compatible missing.store := by
  refine ⟨Encode.blob.from_intoAbstract payload, ?_⟩
  intro lift
  obtain ⟨_, _, choices⟩ := exists_compatible_lift_iff.mp lift
  cases choices with
  | blob hit => cases hit

example : missing.object? () = some (.ref (.blob ())) ∧
    missing.observeRoot? 1 () = some (.ref (.blob ())) := ⟨rfl, rfl⟩

example : ¬ ∃ tree, fullLookup missing.binding () = some tree := by
  rintro ⟨tree, found⟩
  obtain ⟨shallow, hit, expanded⟩ := (fullLookup_eq_some missing.binding).mp found
  have eq : (.ref (.blob ()) : Shallow Unit) = shallow := Option.some.inj hit
  subst shallow
  cases expanded with
  | blob hit => cases hit

example : fullLookup available.binding () = some namedBlob :=
  available.fullLookup_eq_some_iff_observe.mpr ⟨1, rfl⟩

private def aliases (Name : Type) : Reader Name := ⟨fun _ => some .null, fun _ => none⟩

private def collapse : Renaming (aliases Bool).store (aliases Unit).store where
  names := fun _ => ()
  objects := by
    intro _ view hit
    have eq : (.null : Shallow Bool) = view := Option.some.inj hit
    subst view
    rfl
  blobs := by intro _ _ hit; cases hit

private def namedNull {Name : Type} (name : Name) : Named Name := .obj name .null

private theorem valid {Name : Type} (name : Name) : (namedNull name).Compatible (aliases Name).store :=
  ⟨(aliases Name).binding, (Expands.obj rfl Expands.null :
    Expands (aliases Name).store (.ref (.obj name)) (namedNull name)).bindings_subset⟩

example : (namedNull true).erase = (namedNull false).erase := rfl

example : (NamedPER.fromErasure (PER.equality Value) Unit (aliases Unit).store).rel
    ((namedNull true).rename collapse.names) ((namedNull false).rename collapse.names) :=
  (NamedPER.fromErasure_rename_iff (PER.equality Value) collapse (aliases Unit).binding
    (valid true) (valid false)).mpr ⟨valid true, valid false, rfl⟩

example : (NamedPER.onStore (aliases Unit).store (PER.equality (Named Unit))).rel
      ((namedNull true).rename collapse.names) ((namedNull false).rename collapse.names) ∧
    ¬ (NamedPER.onStore (aliases Bool).store (PER.equality (Named Bool))).rel (namedNull true) (namedNull false) := by
  refine ⟨⟨(valid true).rename collapse (aliases Unit).binding, (valid false).rename collapse (aliases Unit).binding,
    rfl⟩, ?_⟩
  intro related
  have same : namedNull true = namedNull false := related.2.2
  cases same

end Silmaril.Formats.Dasl
