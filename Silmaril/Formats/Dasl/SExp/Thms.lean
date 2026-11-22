module

public import Silmaril.Formats.Dasl.SExp.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Formats.Dasl.SExp

@[expose] public section

namespace Silmaril.Formats.Dasl.SExp

open Silmaril.Semantics.Naming (Binding)

variable {Atom Name Ref Item Target : Type} {store : Store Name}

theorem Proper.read_write (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name)
    (item : Formats.SExp Atom) : Proper.read payload (Proper.write (Ref := Ref) payload put item) = some item :=
  Proofs.Formats.Dasl.SExp.proper_read_at_write_at payload put [] item false

theorem Proper.write_embed (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name)
    (item : Formats.SExp Atom) : Named.embed (Proper.write payload put item) = Proper.write payload put item :=
  Proofs.Formats.Dasl.SExp.proper_embed payload put [] item

def Proper.codec (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name) :
    Encode.TotalCodec (Formats.SExp Atom) (Tree Ref Name) :=
  ⟨Proper.write payload put, Proper.read payload, Proper.read_write payload put⟩

theorem Proper.read_mono (payload : Payload Atom) {low high : Partial Name} (step : Extends low high)
    {item : Formats.SExp Atom} (hit : Proper.read payload low = some item) : Proper.read payload high = some item :=
  Proofs.Formats.Dasl.SExp.proper_mono payload step false hit

theorem Dotted.read_write (layout : Dotted.Layout) (payload : Payload Atom) (put : Placement (SExp2 Atom) Name)
    (item : SExp2 Atom) : Dotted.read layout payload (Dotted.write (Ref := Ref) layout payload put item) = some item :=
  Proofs.Formats.Dasl.SExp.dotted_read_at_write_at layout payload put [] item false

def Dotted.codec (layout : Dotted.Layout) (payload : Payload Atom) (put : Placement (SExp2 Atom) Name) :
    Encode.TotalCodec (SExp2 Atom) (Tree Ref Name) :=
  ⟨Dotted.write layout payload put, Dotted.read layout payload, Dotted.read_write layout payload put⟩

theorem Dotted.read_mono (layout : Dotted.Layout) (payload : Payload Atom) {low high : Partial Name}
    (step : Extends low high) {item : SExp2 Atom} (hit : Dotted.read layout payload low = some item) :
    Dotted.read layout payload high = some item := Proofs.Formats.Dasl.SExp.dotted_mono layout payload step false hit

theorem Dotted.transcode_write (source target : Dotted.Layout) (payload : Payload Atom)
    (before after : Placement (SExp2 Atom) Name) (item : SExp2 Atom) :
    Dotted.transcode source target payload after (Dotted.write (Ref := Ref) source payload before item) =
      some (Dotted.write target payload after item) := by
  simp [Dotted.transcode, normalize, Dotted.read_write]

theorem normalize_write (before after : Encode.TotalCodec Item (Tree Ref Name)) (item : Item) :
    normalize before.decode? after.encode (before.encode item) = some (after.encode item) := by
  simp [normalize, before.recovers]

theorem normalize_equal_iff (codec : Encode.TotalCodec Item Target) (read : Tree Ref Name → Option Item)
    {left right : Tree Ref Name} {first second : Item} (leftHit : read left = some first)
    (rightHit : read right = some second) :
    normalize read codec.encode left = normalize read codec.encode right ↔ first = second :=
  Proofs.Formats.Dasl.SExp.norms_equal codec read leftHit rightHit

theorem names_binding (bound : store.Binding) (read : Partial Name → Option Item) : Binding (Names store read) := by
  rintro _ _ _ ⟨first, left, readLeft⟩ ⟨second, right, readRight⟩
  exact Option.some.inj (readLeft.symm.trans (fullNames_binding bound left right ▸ readRight))

theorem observations_agree (bound : store.Binding) (read : Partial Name → Option Item)
    (mono : ∀ ⦃low high item⦄, Extends low high → read low = some item → read high = some item)
    {root : Name} {tree : Named Name} (full : FullNames store root tree) {item : Item} :
    Observes store read root item ↔ read tree.embed = some item :=
  Proofs.Formats.Dasl.SExp.observations_agree bound read mono full

theorem aliases_iff_normalize (bound : store.Binding) (read : Partial Name → Option Item)
    (codec : Encode.TotalCodec Item Target) {left right : Name} {leftTree rightTree : Named Name}
    (leftFull : FullNames store left leftTree) (rightFull : FullNames store right rightTree) :
    Aliases store read left right ↔ ∃ normal,
      normalize read codec.encode leftTree.embed = some normal ∧
      normalize read codec.encode rightTree.embed = some normal :=
  Proofs.Formats.Dasl.SExp.alias_iff_norm bound read codec leftFull rightFull

/-- A finite expanded writer image is publishable exactly with its concrete bindings.
This does not claim an arbitrary proposed allocation is consistent. -/
theorem full_of_bindings {root : Name} (tree : Named Name)
    (stored : store.objects root tree.embed.shallow) (included : tree.embed.bindings.Subset store) :
    FullNames store root tree := ⟨_, stored, Proofs.Formats.Dasl.SExp.expands_of_bindings tree included⟩

end Silmaril.Formats.Dasl.SExp
