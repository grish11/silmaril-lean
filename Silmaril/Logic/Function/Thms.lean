module

public import Silmaril.Logic.Function.Defs
public import Silmaril.Logic.Fragments.Institution.Thms
public import Silmaril.Semantics.Function.Thms
import Silmaril.Proofs.Logic.Function.Institution

@[expose] public section
namespace Silmaril.Logic.Function
open CategoryTheory Silmaril.Logic.Fragments Silmaril.Logic.Institution
open Silmaril.Semantics.Function
open Silmaril.Semantics.Region.Abstract (Closed reindex_closed)
universe u

theorem atom_id {A : Signature.{u}} (atom : Atom A) : Renaming.atom (𝟙 A) atom = atom := Proofs.atom_id atom

theorem atom_comp {A B C : Signature.{u}} (f : A ⟶ B) (g : B ⟶ C) (atom : Atom A) :
    Renaming.atom (f ≫ g) atom = g.atom (f.atom atom) := Proofs.atom_comp f g atom

def atomFunctor : Signature.{u} ⥤ AtomicSignature.{u} where
  obj := atomSignature
  map f := ⟨f.atom⟩
  map_id _ := AtomicSignature.Hom.ext (funext atom_id)
  map_comp f g := AtomicSignature.Hom.ext (funext (atom_comp f g))

def institution : Signature.{u} ⥤ Room.{u,u,u} := atomFunctor ⋙ atomicInstitution

theorem satisfaction {A B : Signature.{u}} (f : A ⟶ B) (model : Model B) (atom : Atom A) :
    f.atom atom ∈ model ↔ atom ∈ reduct f model := Iff.rfl

theorem reduct_laws {A B : Signature.{u}} (f : A ⟶ B) {model : Model B}
    (closed : Closed (Laws B) model) : Closed (Laws A) (reduct f model) :=
  reindex_closed (Proofs.ruleMap f) closed

end Silmaril.Logic.Function
