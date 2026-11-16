module

public import Silmaril.Logic.Algebraic.DependentFamily.Defs
public import Silmaril.Logic.Institution.Hets.PresentationGraph.Thms
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace Silmaril.Logic.Algebraic.DependentFamily.CategoryExample
open CategoryTheory

abbrev arity (_ : Unit) : Nat := 2
abbrev hom {k : Nat} (x y : Fin k) : SortExpr Unit arity k :=
  ⟨(), Fin.cases x (fun _ => y)⟩
@[simp] theorem hom_rename {k l : Nat} (ρ : Fin k → Fin l) (x y : Fin k) :
    (hom x y).rename ρ = hom (ρ x) (ρ y) := by
  apply congrArg (SortExpr.mk ())
  funext i
  change Fin 2 at i
  fin_cases i <;> rfl

abbrev pair {α : Type} (x y : α) : Fin 2 → α := Fin.cases x (fun _ => y)

inductive Operation : (k n : Nat) → (Fin n → SortExpr Unit arity k) →
    SortExpr Unit arity k → Type where
  | identity {k} (x : Fin k) : Operation k 0 Fin.elim0 (hom x x)
  | compose {k} (x y z : Fin k) : Operation k 2 (pair (hom x y) (hom y z)) (hom x z)

def signature : Signature Unit arity := ⟨Operation⟩

/-- Every small category gives an actual model with arrows as dependent fibers. -/
def model (C : Type) [Category.{0} C] : Model signature where
  Base := C
  carrier _ index := index 0 ⟶ index 1
  operation {k n inputs output} op b args := by
    change Operation k n inputs output at op
    cases op with
    | identity x => exact 𝟙 (b x)
    | compose x y z => exact args 0 ≫ args 1

/-- The closed indexed context x,y; f : Hom(x,y). -/
abbrev arrowContext : Fin 1 → SortExpr Unit arity 2 := fun _ => hom 0 1

def arrow : Term signature arrowContext (hom 0 1) := .var 0

def identityAt (x : Fin 2) : Term signature arrowContext (hom x x) :=
  .app (Operation.identity x) id (fun i => Fin.elim0 i)

def leftComposite : Term signature arrowContext (hom 0 1) :=
  .app (Operation.compose 0 0 1) id (Fin.cases (identityAt 0) (fun _ => arrow))

def leftIdentity : Equation signature := ⟨2, 1, arrowContext, hom 0 1, leftComposite, arrow⟩

theorem leftIdentity_satisfied (C : Type) [Category.{0} C] :
    Equation.Satisfies (model C) leftIdentity := by
  change ∀ (b : Fin 2 → C) (v : (i : Fin 1) → b 0 ⟶ b 1), _
  intro b v
  exact Category.id_comp (v 0)

def rightComposite : Term signature arrowContext (hom 0 1) :=
  .app (Operation.compose 0 1 1) id (Fin.cases arrow (fun _ => identityAt 1))

def rightIdentity : Equation signature := ⟨2, 1, arrowContext, hom 0 1, rightComposite, arrow⟩

theorem rightIdentity_satisfied (C : Type) [Category.{0} C] :
    Equation.Satisfies (model C) rightIdentity := by
  change ∀ (b : Fin 2 → C) (v : (i : Fin 1) → b 0 ⟶ b 1), _
  intro b v
  exact Category.comp_id (v 0)

abbrev chainContext : Fin 3 → SortExpr Unit arity 4 :=
  Fin.cases (hom 0 1) (Fin.cases (hom 1 2) (fun _ => hom 2 3))

def compose {k n} {Γ : Fin n → SortExpr Unit arity k} {x y z : Fin k}
    (f : Term signature Γ (hom x y)) (g : Term signature Γ (hom y z)) :
    Term signature Γ (hom x z) :=
  .app (Operation.compose x y z) id (Fin.cases f (fun _ => g))

def associativity : Equation signature :=
  ⟨4, 3, chainContext, hom 0 3,
    compose (compose (.var 0) (.var 1)) (.var 2),
    compose (.var 0) (compose (.var 1) (.var 2))⟩

theorem associativity_satisfied (C : Type) [Category.{0} C] :
    Equation.Satisfies (model C) associativity := by
  change ∀ (b : Fin 4 → C) (v : (i : Fin 3) → (model C).Fiber b (chainContext i)), _
  intro b v
  exact Category.assoc (v 0) (v 1) (v 2)

/-- These are actual equation axioms in the shared presentation category. -/
def presentation : Presentation Unit arity :=
  ⟨signature, {leftIdentity, rightIdentity, associativity}⟩

theorem presentation_satisfied (C : Type) [Category.{0} C] :
    ∀ e ∈ presentation.axioms, Equation.Satisfies (model C) e := by
  intro e he
  rcases he with h | h | h
  · exact h ▸ leftIdentity_satisfied C
  · exact h ▸ rightIdentity_satisfied C
  · exact h ▸ associativity_satisfied C

/-- Shared Hets adapter, with no new graph-specific notion of model. -/
def graph := Silmaril.Logic.Institution.Hets.PresentationGraph.ofPresentation
  (institution Unit arity) presentation

/-- An arbitrary indexed algebra need not satisfy the category laws. -/
def countermodel : Model signature where
  Base := Unit
  carrier _ _ := Bool
  operation {k n inputs output} op _ _ := by
    change Operation k n inputs output at op
    cases op with
    | identity _ => exact false
    | compose _ _ _ => exact true

theorem countermodel_rejects_leftIdentity : ¬ Equation.Satisfies countermodel leftIdentity := by
  intro h
  exact Bool.false_ne_true (h (fun _ => ()) (fun _ => false)).symm

/-- Empty off-diagonal fibers show that the indexing is substantive. -/
theorem discrete_off_diagonal_empty :
    IsEmpty ((model (Discrete Bool)).carrier () (pair ⟨false⟩ ⟨true⟩)) := by
  refine ⟨fun f => ?_⟩
  change (Discrete.mk false ⟶ Discrete.mk true) at f
  exact Bool.false_ne_true (Discrete.eq_of_hom f)

end Silmaril.Logic.Algebraic.DependentFamily.CategoryExample
