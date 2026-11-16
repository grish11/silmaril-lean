module

public import Silmaril.Logic.CommonLogic.Core.FirstOrder.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.CommonLogic.FirstOrder

open Silmaril.Logic.CommonLogic.Core Silmaril.Logic.CommonLogic.Core.FirstOrder
open Silmaril.Logic.Institution.Examples

theorem tuple_eval {S : Signature} {n k m : Nat} (M : Model S)
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (args : Fin m → Expr S n k .individual) :
    (tuple args).eval M ρ σ = List.ofFn (fun i => (args i).eval M ρ σ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (args 0).eval M ρ σ :: (tuple (fun i => args i.succ)).eval M ρ σ = _
    rw [List.ofFn_succ, ih]

theorem term_eval {S : Signature} {n k : Nat} {Γ : Fin n → Unit}
    (M : Model S) (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse) :
    {s : Unit} → (t : EQ.Term (signature S).toSignature Γ s) →
    (term t).eval M ρ σ = t.eval (model M).toAlgebra ρ
  | _, .var _ => rfl
  | _, .app (.name _) _ => rfl
  | _, .app (.apply h _) args => by
    simp only [term, Expr.eval]
    rw [tuple_eval]
    have hargs : (fun i => (term (args i)).eval M ρ σ) =
        (fun i => (args i).eval (model M).toAlgebra ρ) :=
      funext (fun i => term_eval M ρ σ (args i))
    rw [hargs]
    cases h <;> rfl

theorem assignment_eq {D : Type} {n : Nat} (ρ : Fin n → D) (ρ' : Fin (n+1) → D)
    (h : ∀ i, HEq (ρ' i.succ) (ρ i)) : ρ' = Fin.cases (ρ' 0) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact eq_of_heq (h j)

theorem formula_holds {S : Signature} (M : Model S) :
    {n k : Nat} → {Γ : Fin n → Unit} → (p : FOL.Formula (signature S) Γ) →
    (ρ : Fin n → M.Discourse) → (σ : Fin k → List M.Discourse) →
    p.Holds (model M) ρ ↔ (formula p).Holds M ρ σ
  | _, _, _, .eq t u, ρ, σ =>
    (congrArg₂ Eq (term_eval M ρ σ t) (term_eval M ρ σ u)).symm.to_iff
  | _, _, _, .rel (.pred h _) args, ρ, σ => by
    show M.relation (h.eval M) (List.ofFn (fun i => (args i).eval (model M).toAlgebra ρ)) ↔ _
    dsimp only [formula, Formula.Holds]
    rw [tuple_eval]
    have hargs : (fun i => (term (args i)).eval M ρ σ) =
        (fun i => (args i).eval (model M).toAlgebra ρ) := funext (fun i => term_eval M ρ σ (args i))
    rw [hargs]
    cases h <;> rfl
  | _, _, _, .tt, _, _ => Iff.rfl
  | _, _, _, .not p, ρ, σ => not_congr (formula_holds M p ρ σ)
  | _, _, _, .and p q, ρ, σ => and_congr (formula_holds M p ρ σ) (formula_holds M q ρ σ)
  | _, _, _, .all _ p, ρ, σ => by
    constructor
    · intro hall x
      exact (formula_holds M p (Fin.cases x ρ) σ).mp (hall (Fin.cases x ρ) (fun _ => HEq.rfl))
    · intro hall ρ' hagree
      have heq : ρ' = Fin.cases (ρ' 0) ρ := assignment_eq ρ ρ' hagree
      rw [heq]
      exact (formula_holds M p (Fin.cases (ρ' 0) ρ) σ).mpr (hall (ρ' 0))

end Silmaril.Proofs.Logic.CommonLogic.FirstOrder
