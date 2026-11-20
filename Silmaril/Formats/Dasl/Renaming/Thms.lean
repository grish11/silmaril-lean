module

public import Silmaril.Formats.Dasl.Renaming.Defs
public import Silmaril.Formats.Dasl.Thms
import Silmaril.Proofs.Formats.Dasl.Renaming

@[expose] public section

namespace Silmaril.Formats.Dasl

variable {Name Next Last : Type}

@[simp] theorem Named.rename_id (tree : Named Name) : tree.rename id = tree :=
  Proofs.Formats.Dasl.tree_map_id tree

theorem Named.rename_comp (first : Name → Next) (second : Next → Last) (tree : Named Name) :
    (tree.rename first).rename second = tree.rename (second ∘ first) :=
  Proofs.Formats.Dasl.tree_map_comp id id first second tree

@[simp] theorem Named.erase_rename (names : Name → Next) (tree : Named Name) :
    (tree.rename names).erase = tree.erase := Proofs.Formats.Dasl.tree_map_comp id id names (fun _ => ()) tree

theorem Named.embed_rename (names : Name → Next) (tree : Named Name) :
    (tree.rename names).embed = tree.embed.rename names :=
  (Proofs.Formats.Dasl.tree_map_comp id Empty.elim names id tree).trans
    ((congrArg (fun refs => Tree.map refs names tree) (funext fun impossible => impossible.elim)).trans
      (Proofs.Formats.Dasl.tree_map_comp Empty.elim (Link.map names) id names tree).symm)

@[simp] theorem Partial.shallow_rename (names : Name → Next) (tree : Partial Name) :
    (tree.rename names).shallow = Shallow.map names tree.shallow := Proofs.Formats.Dasl.partial_shallow_rename names tree

theorem Named.shallow_rename (names : Name → Next) (tree : Named Name) :
    (tree.rename names).embed.shallow = Shallow.map names tree.embed.shallow :=
  (congrArg Partial.shallow (tree.embed_rename names)).trans (tree.embed.shallow_rename names)

theorem Partial.bindings_rename (names : Name → Next) (tree : Partial Name) :
    (tree.rename names).bindings = Store.renameImage tree.bindings names := Proofs.Formats.Dasl.observed_image names tree

theorem Extends.rename (names : Name → Next) {left right : Partial Name} (step : Extends left right) :
    Extends (left.rename names) (right.rename names) := Proofs.Formats.Dasl.extends_rename names step

variable {source : Store Name} {target : Store Next} {last : Store Last}

theorem Store.renameImage_mono {larger : Store Name} (incl : source.Subset larger) (names : Name → Next) :
    (source.renameImage names).Subset (larger.renameImage names) :=
  ⟨fun _ _ ⟨old, value, hit, eq, mapped⟩ => ⟨old, value, incl.1 hit, eq, mapped⟩,
   fun _ _ ⟨old, hit, eq⟩ => ⟨old, incl.2 hit, eq⟩⟩

theorem Renaming.image_subset (rename : Renaming source target) : (source.renameImage rename.names).Subset target :=
  ⟨fun _ _ ⟨_, _, hit, eq, view⟩ => eq ▸ view ▸ rename.objects hit,
   fun _ _ ⟨_, hit, eq⟩ => eq ▸ rename.blobs hit⟩

def Renaming.ofImage (source : Store Name) (names : Name → Next) : Renaming source (source.renameImage names) :=
  ⟨names, fun {name value} hit => ⟨name, value, hit, rfl, rfl⟩, fun {name _} hit => ⟨name, hit, rfl⟩⟩

def Renaming.id (source : Store Name) : Renaming source source :=
  ⟨fun name => name, fun {_ value} hit => (Shallow.map_id value).symm ▸ hit, fun {_ _} hit => hit⟩

def Renaming.comp (first : Renaming source target) (second : Renaming target last) : Renaming source last :=
  ⟨second.names ∘ first.names,
   fun {_ value} hit => Shallow.map_comp _ _ value ▸ second.objects (first.objects hit),
   fun {_ _} hit => second.blobs (first.blobs hit)⟩

@[simp] theorem Renaming.id_comp (rename : Renaming source target) : (Renaming.id source).comp rename = rename := by
  cases rename; rfl

@[simp] theorem Renaming.comp_id (rename : Renaming source target) : rename.comp (Renaming.id target) = rename := by
  cases rename; rfl

theorem Renaming.comp_assoc {Final : Type} {final : Store Final} (first : Renaming source target)
    (second : Renaming target last) (third : Renaming last final) :
    (first.comp second).comp third = first.comp (second.comp third) := rfl

theorem Renaming.collapsed_objects (rename : Renaming source target) (bound : target.Binding)
    {left right : Name} {first second : Shallow Name} (same : rename.names left = rename.names right)
    (hit : source.objects left first) (other : source.objects right second) :
    Shallow.map rename.names first = Shallow.map rename.names second :=
  bound.1 (same ▸ rename.objects hit) (rename.objects other)

theorem Renaming.collapsed_blobs (rename : Renaming source target) (bound : target.Binding)
    {left right : Name} {first second : ByteArray} (same : rename.names left = rename.names right)
    (hit : source.blobs left first) (other : source.blobs right second) : first = second :=
  bound.2 (same ▸ rename.blobs hit) (rename.blobs other)

theorem Renaming.bindings_subset (rename : Renaming source target) {tree : Partial Name}
    (admitted : tree.bindings.Subset source) : (tree.rename rename.names).bindings.Subset target :=
  (tree.bindings_rename rename.names).symm ▸ ⟨fun _ _ hit => rename.image_subset.1 ((Store.renameImage_mono admitted _).1 hit),
    fun _ _ hit => rename.image_subset.2 ((Store.renameImage_mono admitted _).2 hit)⟩

theorem Renaming.preserves_valid (rename : Renaming source target) (bound : target.Binding) {tree : Named Name}
    (admitted : tree.embed.bindings.Subset source) :
    target.Binding ∧ (tree.rename rename.names).embed.bindings.Subset target :=
  ⟨bound, (tree.embed_rename rename.names).symm ▸ rename.bindings_subset admitted⟩

theorem Expands.rename {shallow : Shallow Name} {tree : Named Name} (expanded : Expands source shallow tree)
    (rename : Renaming source target) : Expands target (Shallow.map rename.names shallow) (tree.rename rename.names) :=
  Proofs.Formats.Dasl.expands_rename rename expanded

end Silmaril.Formats.Dasl
