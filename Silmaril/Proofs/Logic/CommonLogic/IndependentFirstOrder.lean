module

public import Silmaril.Logic.CommonLogic.FirstOrder.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder

open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic.FirstOrder

/-- Finite tuple evaluation; adapted from the existing named-head fragment proof. -/
theorem tuple_eval {S : Core.Signature} {n k m : Nat} (M : Core.Model S)
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (args : Fin m → Core.Expr S n k .individual) :
    (tuple args).eval M ρ σ = List.ofFn (fun i => (args i).eval M ρ σ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (args 0).eval M ρ σ :: (tuple (fun i => args i.succ)).eval M ρ σ = _
    rw [List.ofFn_succ, ih]

/-- The public FOL quantifier assignment convention agrees with CL's first-variable binder. -/
theorem assignment_eq {D : Type} {n : Nat} (ρ : Fin n → D) (ρ' : Fin (n+1) → D)
    (h : ∀ i, HEq (ρ' i.succ) (ρ i)) : ρ' = Fin.cases (ρ' 0) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact eq_of_heq (h j)

theorem tuple_map {S T : Core.Signature} (f : S ⟶ T) {n k m : Nat}
    (args : Fin m → Core.Expr S n k .individual) :
    (tuple args).map f = tuple (fun i => (args i).map f) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg₂ Core.Expr.cons rfl (ih _)

theorem term_map {S T : Signature} (f : S ⟶ T) {n k : Nat} {Γ : Fin n → Unit} :
    {s : Unit} → (t : EQ.Term (publicSignature S).toSignature Γ s) →
    (term (k := k) t).map (clMap f) = term (t.map (publicMap f).toHom)
  | _, .var _ => rfl
  | _, .app o args => by
    dsimp only [term, Core.Expr.map, EQ.Term.map]
    rw [tuple_map]
    exact congrArg (Core.Expr.app _) (congrArg tuple (funext fun i => term_map f (args i)))

theorem formula_map {S T : Signature} (f : S ⟶ T) : {n k : Nat} → {Γ : Fin n → Unit} →
    (p : FOL.Formula (publicSignature S) Γ) →
    (formula (k := k) p).map (clMap f) = formula (p.map (publicMap f))
  | _, _, _, .eq t u => congrArg₂ Core.Formula.equal (term_map f t) (term_map f u)
  | _, _, _, .rel r args => by
    dsimp only [formula, Core.Formula.map, Core.Expr.map, FOL.Formula.map]
    rw [tuple_map]
    exact congrArg (Core.Formula.pred _) (congrArg tuple (funext fun i => term_map f (args i)))
  | _, _, _, .tt => rfl
  | _, _, _, .not p => congrArg Core.Formula.neg (formula_map f p)
  | _, _, _, .and p q => congrArg₂ Core.Formula.conj (formula_map f p) (formula_map f q)
  | _, _, _, .all _ p => congrArg Core.Formula.all (formula_map f p)

theorem term_eval {S : Signature} {n k : Nat} {Γ : Fin n → Unit}
    (M : Core.Model (clSignature S)) (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse) :
    {s : Unit} → (t : EQ.Term (publicSignature S).toSignature Γ s) →
    (term t).eval M ρ σ = t.eval (decode M).toAlgebra ρ
  | _, .var _ => rfl
  | _, .app o args => by
    simp only [term, Core.Expr.eval]
    rw [tuple_eval]
    exact congrArg (M.function _) (congrArg List.ofFn (funext fun i => term_eval M ρ σ (args i)))

theorem formula_holds {S : Signature} (M : Core.Model (clSignature S)) :
    {n k : Nat} → {Γ : Fin n → Unit} → (p : FOL.Formula (publicSignature S) Γ) →
    (ρ : Fin n → M.Discourse) → (σ : Fin k → List M.Discourse) →
    p.Holds (decode M) ρ ↔ (formula p).Holds M ρ σ
  | _, _, _, .eq t u, ρ, σ =>
    (congrArg₂ Eq (term_eval M ρ σ t) (term_eval M ρ σ u)).symm.to_iff
  | _, _, _, .rel r args, ρ, σ => by
    dsimp only [formula, Core.Formula.Holds, Core.Expr.eval]
    rw [tuple_eval]
    exact (congrArg (M.relation _) (congrArg List.ofFn
      (funext fun i => term_eval M ρ σ (args i)))).symm.to_iff
  | _, _, _, .tt, _, _ => Iff.rfl
  | _, _, _, .not p, ρ, σ => not_congr (formula_holds M p ρ σ)
  | _, _, _, .and p q, ρ, σ => and_congr (formula_holds M p ρ σ) (formula_holds M q ρ σ)
  | _, _, _, .all _ p, ρ, σ => by
    constructor
    · intro hall x
      exact (formula_holds M p (Fin.cases x ρ) σ).mp (hall (Fin.cases x ρ) (fun _ => HEq.rfl))
    · intro hall ρ' hagree
      have heq := assignment_eq ρ ρ' hagree
      rw [heq]
      exact (formula_holds M p (Fin.cases (ρ' 0) ρ) σ).mpr (hall (ρ' 0))

end Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder
