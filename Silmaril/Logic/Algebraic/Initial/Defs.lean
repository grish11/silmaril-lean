module

public import Silmaril.Logic.Institution.Examples.Equational
public import Silmaril.Logic.Institution.Structured.Constraints.Institution
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! Initial/free algebra semantics use actual public EQ algebras and terms.
The constraint construction is Durán–Meseguer (1999), Definition 4.14;
the term universal property is Goguen–Burstall (1992), Appendix A1, Theorem 55.
No initiality or satisfaction certificate is stored in an algebra. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- Only the sentence universe changes: constraints quantify over signatures.
Carriers, operations, morphisms and satisfaction are exactly public EQ. -/
def equationalRoom (A : EQ.Signature) : Room.{1,0,1} :=
  ⟨ULift.{1} (EQ.Equation A), Cat.of (EQ.Algebra A), fun M e => e.down.Holds M⟩

def equationalCorridor {A B : EQ.Signature} (f : A ⟶ B) : equationalRoom A ⟶ equationalRoom B :=
  ⟨fun e => ⟨e.down.map f⟩, EQ.Algebra.reduct f, fun M e => EQ.Equation.holds_map f M e.down⟩

def equational : EQ.Signature ⥤ Room.{1,0,1} where
  obj := equationalRoom
  map := equationalCorridor
  map_id _ := Room.hom_ext (funext fun e => congrArg ULift.up (EQ.Equation.map_id e.down)) rfl
  map_comp f g := Room.hom_ext
    (funext fun e => congrArg ULift.up (EQ.Equation.map_comp f g e.down)) rfl

/-- Actual existing constraint institution: its models remain all EQ algebras. -/
abbrev institution : EQ.Signature ⥤ Room.{1,0,1} := Constraints.institution equational
abbrev Constraint (A : EQ.Signature) := Constraints.Constraint equational A
abbrev Theory := Spec equational
abbrev Models (T : Theory) := SemanticModels.Models equational T

abbrev emptySignature : EQ.Signature := ⟨PEmpty, fun _ _ _ => PEmpty⟩

def emptyMap (A : EQ.Signature) : emptySignature ⟶ A :=
  ⟨PEmpty.elim, fun o => o.elim⟩

abbrev emptyTheory : Theory := ⟨emptySignature, ∅⟩

def emptyTheoryMap (T : Theory) : emptyTheory ⟶ T :=
  ⟨emptyMap T.sig, fun _ h => h.elim⟩

/-- An actual freeness constraint out of the empty theory, in identity context. -/
def initialConstraint (T : Theory) : Constraint T.sig :=
  ⟨emptyTheory, T, emptyTheoryMap T, 𝟙 T.sig⟩

/-- Constructor algebra on the existing public finite-context syntax. -/
def termAlgebra (A : EQ.Signature) {k : Nat} (Γ : Fin k → A.S) : EQ.Algebra A where
  carrier s := EQ.Term A Γ s
  op o args := .app o args

/-- The actual evaluation homomorphism extends a variable assignment. -/
def foldHom {A : EQ.Signature} {k : Nat} {Γ : Fin k → A.S} (M : EQ.Algebra A)
    (v : ∀ i, M.carrier (Γ i)) : termAlgebra A Γ ⟶ M :=
  ⟨fun _ t => t.eval M v, fun _ _ => rfl⟩

abbrev closedContext (A : EQ.Signature) : Fin 0 → A.S := Fin.elim0
abbrev closedAlgebra (A : EQ.Signature) := termAlgebra A (closedContext A)

end Silmaril.Logic.Algebraic.Initial
