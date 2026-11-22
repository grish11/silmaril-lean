module

public import Silmaril.Formats.Dasl.PairedShallow.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
public import Silmaril.Formats.Dasl.Thms
import Silmaril.Proofs.Formats.Dasl.PairedShallow

public section

namespace Silmaril.Formats.Dasl

theorem Shallow.directLinks_map_iff {Name Next : Type} (names : Name → Next) (tree : Shallow Name) (link : Link Next) :
    link ∈ (Shallow.map names tree).directLinks ↔
      ∃ old, old ∈ tree.directLinks ∧ Link.map names old = link :=
  Proofs.Formats.Dasl.direct_links_map_iff names tree link

namespace PairedShallow

variable {Concrete Abstract : Type}

@[simp] theorem concrete_ofConcrete (names : Concrete → Abstract) (tree : Shallow Concrete) :
    (ofConcrete names tree).concrete = tree :=
  (Shallow.map_comp _ Prod.fst tree).trans (Shallow.map_id tree)

@[simp] theorem abstract_ofConcrete (names : Concrete → Abstract) (tree : Shallow Concrete) :
    (ofConcrete names tree).abstract = Shallow.map names tree := Shallow.map_comp _ Prod.snd tree

theorem ofConcrete_agrees (names : Concrete → Abstract) (tree : Shallow Concrete) :
    (ofConcrete names tree).AgreesBy names := by
  intro link present
  obtain ⟨old, _, rfl⟩ := (tree.directLinks_map_iff _ link).mp present
  cases old <;> rfl

@[simp] theorem concrete_diagonal (tree : Shallow Concrete) : (diagonal tree).concrete = tree :=
  concrete_ofConcrete id tree

@[simp] theorem abstract_diagonal (tree : Shallow Concrete) : (diagonal tree).abstract = tree :=
  (abstract_ofConcrete id tree).trans (Shallow.map_id tree)

theorem diagonal_agrees (tree : Shallow Concrete) : (diagonal tree).AgreesBy id :=
  ofConcrete_agrees id tree

theorem AbstractValid.unique {tree : PairedShallow Concrete Abstract} {store : Store Abstract}
    (valid : tree.AbstractValid store) : ∃! value, Expands store tree.abstract value :=
  let ⟨bound, value, expanded⟩ := valid
  ⟨value, expanded, fun _ other => other.unique bound expanded⟩

theorem AbstractValid.fullNames {tree : PairedShallow Concrete Abstract} {store : Store Abstract}
    (valid : tree.AbstractValid store) {root : Abstract} (stored : store.objects root tree.abstract) :
    ∃ value, FullNames store root value :=
  let ⟨_, value, expanded⟩ := valid
  ⟨value, tree.abstract, stored, expanded⟩

end PairedShallow
end Silmaril.Formats.Dasl
