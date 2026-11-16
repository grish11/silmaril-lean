module

public import Silmaril.Logic.Algebraic.ManySorted.Varying.Thms

/-! Sort-changing controls for the full public/private correspondence. -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.ManySorted.Varying.Examples
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

def pure (S : Type) : Signature := ⟨S, ⟨fun _ _ _ => Empty⟩⟩
def pureMap {S T : Type} (f : S → T) : pure S ⟶ pure T :=
  ⟨f, fun op => Empty.elim op⟩
def pureModel (S : Type) (F : S → Type) : Model (pure S) :=
  ⟨F, fun op => Empty.elim op⟩

def collapse : pure Bool ⟶ pure Unit := pureMap (fun _ => ())
def swap : pure Bool ⟶ pure Bool := pureMap Bool.not

/-- Two variables at false remain different indices; a third declared variable
at true tests the universal context even though neither term uses it. -/
def collisionEquation : Equation (pure Bool) where
  variableCount := 3
  context i := if i = 2 then true else false
  sort := false
  lhs := .var 0
  rhs := .var 1

theorem collapse_keeps_variable_indices :
    (mapEquation collapse collisionEquation).variableCount = 3 ∧
      (mapEquation collapse collisionEquation).context = (fun _ => ()) := ⟨rfl, rfl⟩

/-- Sort identification does not identify the two independently assigned variables. -/
theorem collision_false :
    ¬ ManySorted.Equation.Satisfies (pureModel Unit (fun _ => Bool))
      (mapEquation collapse collisionEquation) := by
  intro h
  change ∀ ρ : Fin 3 → Bool, ρ 0 = ρ 1 at h
  have bad : false = true := h (fun i => if i = 0 then false else true)
  cases bad

/-- Empty declared sorts make universal equations vacuous, including unused variables. -/
def separated : Model (pure Bool) := pureModel Bool (fun s => if s then Empty else Bool)

theorem empty_context_vacuous : ManySorted.Equation.Satisfies separated collisionEquation := by
  unfold ManySorted.Equation.Satisfies collisionEquation
  intro ρ
  exact Empty.elim (ρ 2)

/-- A sort collision need not admit strict model expansion: its two reduct
carriers must coincide, but this source model has Bool and Empty carriers. -/
theorem collapse_not_model_expansive : ¬ ∃ M : Model (pure Unit), reduct collapse M = separated := by
  rintro ⟨M, h⟩
  have carriers : separated.carrier false = separated.carrier true := by
    calc
      separated.carrier false = (reduct collapse M).carrier false :=
        congrArg (fun N => N.carrier false) h.symm
      _ = (reduct collapse M).carrier true := rfl
      _ = separated.carrier true := congrArg (fun N => N.carrier true) h
  exact Empty.elim (cast carriers false)

/-- A permutation changes the sort in both directions. -/
theorem swap_changes_sorts : swap.sorts false = true ∧ swap.sorts true = false := ⟨rfl, rfl⟩

/-- A target can add an empty sort; the reduct retains only the selected one. -/
def addSort : pure Unit ⟶ pure Bool := pureMap (fun _ => false)
theorem added_empty_sort :
    (reduct addSort separated).carrier () = Bool ∧ separated.carrier true = Empty := ⟨rfl, rfl⟩

/-- The reduct includes a homomorphism that collapses distinct carrier elements. -/
def collapseValues : pureModel Unit (fun _ => Bool) ⟶ pureModel Unit (fun _ => Unit) :=
  ⟨fun _ _ => (), fun op => Empty.elim op⟩

theorem reduct_keeps_noninjective_hom :
    ((reductFunctor collapse).map collapseValues).map false false =
      ((reductFunctor collapse).map collapseValues).map false true ∧
      (false : Bool) ≠ true := ⟨rfl, Bool.false_ne_true⟩

/-- Every arity is populated here, so both variable and application clauses
of the translation/evaluator occur without restricting the term constructors. -/
def populated (S : Type) : Signature := ⟨S, ⟨fun _ _ _ => Unit⟩⟩
def populatedMap : populated Bool ⟶ populated Unit := ⟨fun _ => (), fun op => op⟩
def populatedModel : Model (populated Unit) := ⟨fun _ => Bool, fun _ _ => false⟩
def constant : Term (populated Bool) (fun _ : Fin 0 => false) true :=
  .app (inputs := Fin.elim0) () (fun i => Fin.elim0 i)

theorem constant_changes_sort :
    populatedModel.eval Fin.elim0 (mapTerm populatedMap constant) = false := rfl

/-- Actual public arbitrary-sort map, not just a private identity-sort control. -/
def publicCollapse : EQ.Signature.Hom (publicSignature (pure Bool))
    (publicSignature (pure Unit)) := ⟨fun _ => (), fun op => Empty.elim op⟩

theorem actual_public_collision :
    toEquation ((fromEquation collisionEquation).map publicCollapse) =
      mapEquation collapse collisionEquation :=
  (toEquation_map collapse (fromEquation collisionEquation)).trans
    (congrArg (mapEquation collapse) (to_fromEquation collisionEquation))

end Silmaril.Logic.Algebraic.ManySorted.Varying.Examples
