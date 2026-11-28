module

public import Silmaril.Logic.Institution.Generalized.Thms
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Functor.Const

@[expose] public section

/-! # Generalized institution examples

The typed example uses distinct syntax for four denotations. The lax example
gives a strict change of value along the map from signature zero to one.
-/

namespace Silmaril.Logic.Institution.Generalized.Examples

open CategoryTheory Opposite

/-- The type codes of a small typed language. -/
inductive Code where
  | proposition
  | number
  | verdict
  | evidence

/-- Denotations include an actual Lean proposition and two kinds of verdict. -/
abbrev denote : Code → Type
  | .proposition => Prop
  | .number => Nat
  | .verdict => Option Bool
  | .evidence => Evidence

/-- Observe a Boolean model through four different types of syntax. -/
def typed : TypedInstitution Nat denote where
  Sen
    | .proposition => (Functor.const Nat).obj Unit
    | .number => (Functor.const Nat).obj Bool
    | .verdict => (Functor.const Nat).obj (Option Unit)
    | .evidence => (Functor.const Nat).obj (Set Bool)
  Mod := (Functor.const Natᵒᵖ).obj (Cat.of (Discrete Bool))
  eval
    | .proposition, _, M, _ => M.as = true
    | .number, _, M, b => if M.as = b then 1 else 0
    | .verdict, _, M, q => q.map (fun _ => M.as)
    | .evidence, _, M, completions => Evidence.ofCompletions completions (· = M.as)
  eval_map := by
    intro t S T σ M φ
    cases t <;> rfl

example : (typed.propInstitution .proposition (Equiv.refl Prop)).Sat 0 (Discrete.mk true) () := rfl

example : ¬ (typed.propInstitution .proposition (Equiv.refl Prop)).Sat 0 (Discrete.mk false) () :=
  Bool.noConfusion

example : typed.eval .verdict 0 (Discrete.mk true) none = none := rfl

example : typed.eval .verdict 0 (Discrete.mk true) (some ()) = some true := rfl

example : typed.eval .verdict 0 (Discrete.mk false) (some ()) = some false := rfl

example : typed.eval .evidence 0 (Discrete.mk true) (∅ : Set Bool) = ⟨True, True⟩ :=
  Evidence.ofCompletions_empty _

example : typed.eval .evidence 0 (Discrete.mk true) ({true} : Set Bool) = ⟨True, False⟩ := by
  change Evidence.ofCompletions {true} (· = true) = _
  simp [Evidence.ofCompletions_singleton]

example : typed.eval .evidence 0 (Discrete.mk true) ({false} : Set Bool) = ⟨False, True⟩ := by
  change Evidence.ofCompletions {false} (· = true) = _
  simp [Evidence.ofCompletions_singleton]

example : typed.eval .evidence 0 (Discrete.mk true) Set.univ = ⟨False, False⟩ :=
  Evidence.ofCompletions_mixed (x := true) (y := false) trivial trivial rfl Bool.noConfusion

example : (typed.atType .number).eval 0 (Discrete.mk true) true = 1 := rfl

example : (typed.atType .number).eval 0 (Discrete.mk false) true = 0 := rfl

-- Both distinct data values pass the same exact cut.
example : ((typed.atType .number).cut 0).Sat 0 (Discrete.mk true) true ∧
    ((typed.atType .number).cut 0).Sat 0 (Discrete.mk false) true :=
  ⟨Nat.zero_le _, Nat.zero_le _⟩

-- The empty premise set has both Boolean models. The conclusion is mixed.
example : ((typed.atType .proposition).toEvaluation.entailmentEvidence id
    (S := 0) ∅ ()) = ⟨False, False⟩ :=
  Evidence.ofCompletions_mixed (x := Discrete.mk true) (y := Discrete.mk false)
    (fun _ h => False.elim h) (fun _ h => False.elim h) rfl Bool.noConfusion

/-- Signature numbers serve as the evaluation. A morphism is an ordering proof. -/
def lax : LaxInstitution Nat Nat where
  Sen := (Functor.const Nat).obj Unit
  Mod := (Functor.const Natᵒᵖ).obj (Cat.of (Discrete Unit))
  eval S _ _ := S
  le_eval_map σ _ _ := leOfHom σ

/-- Threshold zero reflects because every value passes the cut. -/
theorem lax_reflects_zero : lax.ReflectsCut 0 :=
  fun _ _ _ _ => Nat.zero_le _

example : (lax.cut 0 lax_reflects_zero).Sat 1 (Discrete.mk ()) () := Nat.zero_le _

/-- Threshold one passes in the target and fails in the reduct along zero to one. -/
theorem lax_does_not_reflect_one : ¬ lax.ReflectsCut 1 := by
  intro h
  exact Nat.not_succ_le_zero 0 (h (homOfLE Nat.zero_lt_one.le) (Discrete.mk ()) () le_rfl)

end Silmaril.Logic.Institution.Generalized.Examples
