module

public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Mathlib.Data.List.Basic
public import Silmaril.Logic.Institution.Morphism

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {A B C : Signature S}

/-- Equality atoms in one shared, sorted variable context. -/
structure Atom (A : Signature S) {k} (Γ : Fin k → S) where
  sort : S
  lhs : Term A Γ sort
  rhs : Term A Γ sort

namespace Atom
variable {k} {Γ : Fin k → S}
def map (f : A ⟶ B) (a : Atom A Γ) : Atom B Γ :=
  ⟨a.sort, Term.map f a.lhs, Term.map f a.rhs⟩
def Holds (M : Model A) (v : ∀ i, M.carrier (Γ i)) (a : Atom A Γ) : Prop :=
  M.eval v a.lhs = M.eval v a.rhs
@[simp] theorem map_id (a : Atom A Γ) : map (𝟙 A) a = a := by cases a; simp [map]
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (a : Atom A Γ) :
    map (f ≫ g) a = map g (map f a) := by cases a; simp [map]
theorem satisfaction (f : A ⟶ B) (M : Model B) (v : ∀ i, M.carrier (Γ i)) (a : Atom A Γ) :
    Holds M v (map f a) ↔ Holds (Signature.Hom.reduct f M) v a := by
  simp only [Holds, map, Signature.Hom.eval_map]
  rfl
end Atom

/-- A universal equational Horn clause. An empty premise list is allowed. -/
structure Horn (A : Signature S) where
  variableCount : Nat
  context : Fin variableCount → S
  premises : List (Atom A context)
  conclusion : Atom A context

namespace Horn
def map (f : A ⟶ B) (h : Horn A) : Horn B :=
  ⟨h.variableCount, h.context, h.premises.map (Atom.map f), Atom.map f h.conclusion⟩
def Satisfies (M : Model A) (h : Horn A) : Prop :=
  ∀ v : (i : Fin h.variableCount) → M.carrier (h.context i),
    (∀ a ∈ h.premises, Atom.Holds M v a) → Atom.Holds M v h.conclusion
@[simp] theorem map_id (h : Horn A) : map (𝟙 A) h = h := by
  have hmap : (Atom.map (𝟙 A) : Atom A h.context → _) = id := funext Atom.map_id
  cases h
  simp [map, hmap]
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (h : Horn A) :
    map (f ≫ g) h = map g (map f h) := by
  have hmap : (Atom.map (f ≫ g) : Atom A h.context → _) = Atom.map g ∘ Atom.map f :=
    funext (Atom.map_comp f g)
  cases h
  simp only [map, Atom.map_comp, List.map_map, hmap]

theorem satisfaction (f : A ⟶ B) (M : Model B) (h : Horn A) :
    Satisfies M (map f h) ↔ Satisfies (Signature.Hom.reduct f M) h := by
  change (∀ v : (i : Fin h.variableCount) → M.carrier (h.context i),
    (∀ a ∈ h.premises.map (Atom.map f), Atom.Holds M v a) →
      Atom.Holds M v (Atom.map f h.conclusion)) ↔ _
  simp only [List.forall_mem_map, Atom.satisfaction]
  rfl

def ofEquation (e : Equation A) : Horn A :=
  ⟨e.variableCount, e.context, [], ⟨e.sort, e.lhs, e.rhs⟩⟩
theorem ofEquation_satisfaction (M : Model A) (e : Equation A) :
    Satisfies M (ofEquation e) ↔ Equation.Satisfies M e := by
  constructor
  · intro h v
    exact h v (fun a membership => nomatch membership)
  · intro h v _
    exact h v
end Horn

def hornInstitution (S : Type) : Signature S ⥤ Room where
  obj A := ⟨Horn A, Cat.of (Model A), Horn.Satisfies⟩
  map f := ⟨Horn.map f, Signature.Hom.reductFunctor f, Horn.satisfaction f⟩
  map_id _ := by
    apply Room.hom_ext
    · funext h; exact Horn.map_id h
    · exact Signature.Hom.reductFunctor_id
  map_comp f g := by
    apply Room.hom_ext
    · funext h; exact Horn.map_comp f g h
    · exact Signature.Hom.reductFunctor_comp f g

abbrev HornPresentation (S : Type) := Silmaril.Logic.Institution.Presentation (hornInstitution S)
abbrev HornTheory (S : Type) := Silmaril.Logic.Institution.Theory (hornInstitution S)
end Silmaril.Logic.Algebraic.ManySorted

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
open CategoryTheory Silmaril.Logic.Institution

/-- Equations embed as Horn clauses with no premises, naturally in signatures. -/
def equationToHorn (S : Type) : institution S ⟶ hornInstitution S where
  app A :=
    { sen := Horn.ofEquation
      mod := 𝟭 (Model A)
      sat := Horn.ofEquation_satisfaction }
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext e; rfl
    · rfl
end Silmaril.Logic.Algebraic.ManySorted

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
open CategoryTheory Silmaril.Logic.Institution

def equationalInst (S : Type) : Inst := ⟨Signature S, institution S⟩
def hornInst (S : Type) : Inst := ⟨Signature S, hornInstitution S⟩

/-- The universal Horn extension is a genuine institution comorphism. -/
def equationHornComorphism (S : Type) : Inst.CoHom (equationalInst S) (hornInst S) where
  Φ := 𝟭 _
  ρ := equationToHorn S ≫ (Functor.leftUnitor (hornInstitution S)).inv
end Silmaril.Logic.Algebraic.ManySorted

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
open CategoryTheory Silmaril.Logic.Institution

/-- Algebraic theories themselves are signatures, with their categories of satisfying models. -/
def theoryInstitution (S : Type) : Theory S ⥤ Room :=
  Silmaril.Logic.Institution.Theory.institution (institution S)

def hornTheoryInstitution (S : Type) : HornTheory S ⥤ Room :=
  Silmaril.Logic.Institution.Theory.institution (hornInstitution S)
end Silmaril.Logic.Algebraic.ManySorted
