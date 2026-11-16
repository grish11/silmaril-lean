module

public import Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Thms
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.ManySorted.PublicEQ
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {S : Type} {A : Signature S}

def publicInstitution (S : Type) : Signature S ⥤ Room := signatures S ⋙ EQ.institution
def publicInst (S : Type) : Inst := ⟨Signature S, publicInstitution S⟩
def manySortedInst (S : Type) : Inst := ⟨Signature S, institution S⟩

def forwardCorridor (A : Signature S) :
    (publicInstitution S).obj A ⟶ (institution S).obj A :=
  ⟨toEquation, fromModels A, satisfaction⟩

def forwardNatural (S : Type) : publicInstitution S ⟶ institution S where
  app := forwardCorridor
  naturality := by
    intro A B f
    exact Room.hom_ext (funext fun e => toEquation_map f e) (fromModels_reduct f)

/-- A typed bridge from actual public EQ restricted to fixed sorts, with exact expansion. -/
def toManySorted (S : Type) : Inst.CoHom (publicInst S) (manySortedInst S) where
  Φ := 𝟭 _
  ρ := forwardNatural S ≫ (Functor.leftUnitor (institution S)).inv

theorem toManySorted_modelExpansive (S : Type) : (toManySorted S).ModelExpansive :=
  fun _ M => ⟨toModel M, from_toModel M⟩

def reverseCorridor (A : Signature S) :
    (institution S).obj A ⟶ (publicInstitution S).obj A :=
  ⟨fromEquation, toModels A, reverse_satisfaction⟩

def reverseNatural (S : Type) : institution S ⟶ publicInstitution S where
  app := reverseCorridor
  naturality := by
    intro A B f
    exact Room.hom_ext (funext fun e => fromEquation_map f e) (toModels_reduct f)

def toPublicEQ (S : Type) : Inst.CoHom (manySortedInst S) (publicInst S) where
  Φ := 𝟭 _
  ρ := reverseNatural S ≫ (Functor.leftUnitor (publicInstitution S)).inv

theorem toPublicEQ_modelExpansive (S : Type) : (toPublicEQ S).ModelExpansive :=
  fun _ M => ⟨fromModel M, to_fromModel M⟩

theorem entails_iff (H : Set (EQ.Equation (signature A))) (e : EQ.Equation (signature A)) :
    (EQ.room (signature A)).Entails H e ↔
      ((institution S).obj A).Entails (toEquation '' H) (toEquation e) :=
  (toManySorted S).entails_iff (toManySorted_modelExpansive S) A H e

/-- Satisfiability is preserved and reflected for the translated theory. -/
theorem sat_iff (H : Set (EQ.Equation (signature A))) :
    (∃ M : EQ.Algebra (signature A), ∀ e ∈ H, e.Holds M) ↔
      ∃ M : Model A, ∀ e ∈ H, Equation.Satisfies M (toEquation e) := by
  constructor
  · rintro ⟨M, h⟩
    refine ⟨toModel M, fun e he => ?_⟩
    apply (satisfaction _ _).2
    rw [from_toModel]
    exact h e he
  · rintro ⟨M, h⟩
    exact ⟨fromModel M, fun e he => (satisfaction _ _).1 (h e he)⟩

theorem unsat_iff (H : Set (EQ.Equation (signature A))) :
    (¬ ∃ M : EQ.Algebra (signature A), ∀ e ∈ H, e.Holds M) ↔
      ¬ ∃ M : Model A, ∀ e ∈ H, Equation.Satisfies M (toEquation e) :=
  not_congr (sat_iff H)

end Silmaril.Logic.Algebraic.ManySorted.PublicEQ
