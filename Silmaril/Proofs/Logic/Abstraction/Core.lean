module

public import Silmaril.Logic.Abstraction.Defs

public section

namespace Silmaril.Proofs.Logic.Abstraction

open CategoryTheory Silmaril.Logic.Abstraction

variable {S T U : Signature}

theorem map_id {k : Nat} (t : Term S k) : t.map (𝟙 S) = t := by
  induction t with
  | bound => rfl
  | free x args ih => exact congrArg (Term.free x) (funext ih)
  | app a args ih => exact congrArg (Term.app a) (funext ih)

theorem map_comp (f : S ⟶ T) (g : T ⟶ U) {k : Nat} (t : Term S k) :
    t.map (f ≫ g) = (t.map f).map g := by
  induction t with
  | bound => rfl
  | free x args ih => exact congrArg (Term.free x) (funext ih)
  | app a args ih => exact congrArg (Term.app (g.symbol (f.symbol a))) (funext ih)

theorem eval_map (f : S ⟶ T) (A : Algebra T) (ν : Valuation A.Carrier)
    {k : Nat} (t : Term S k) (env : Fin k → A.Carrier) :
    (t.map f).eval A ν env = t.eval (A.reduct f) ν env := by
  induction t with
  | bound => rfl
  | free x args ih => exact congrArg (ν _ x) (funext fun i => ih i env)
  | app a args ih =>
    exact congrArg (A.op (f.symbol a)) (funext fun i => funext fun values =>
      ih i (Fin.addCases env values))

theorem substValuation_map (f : S ⟶ T) (A : Algebra T) (ν : Valuation A.Carrier)
    (σ : Substitution S) :
    A.substValuation ν (σ.map f) = (A.reduct f).substValuation ν σ := by
  funext n x args
  unfold Algebra.substValuation Substitution.map
  cases h : σ n x with
  | none => rfl
  | some t => exact eval_map f A ν t args

theorem rule_map_id (r : Rule S) : r.map (𝟙 S) = r := by
  have hp : Premise.map (𝟙 S) = id := by
    funext p
    exact congrArg (Sigma.mk p.1) (map_id p.2)
  simp [Rule.map, hp, map_id]

theorem rule_map_comp (f : S ⟶ T) (g : T ⟶ U) (r : Rule S) :
    r.map (f ≫ g) = (r.map f).map g := by
  have hp : Premise.map (f ≫ g) = Premise.map g ∘ Premise.map f := by
    funext p
    exact congrArg (Sigma.mk p.1) (map_comp f g p.2)
  simp [Rule.map, hp, map_comp, List.map_map]

theorem holdsAt_map (f : S ⟶ T) (A : Algebra T) (O : LogicalOrder A.Carrier)
    (ν : Valuation A.Carrier) (r : Rule S) :
    (r.map f).HoldsAt A O ν ↔ r.HoldsAt (A.reduct f) O ν := by
  simp only [Rule.HoldsAt, Rule.map, List.forall_mem_map, Premise.map, eval_map]
  rfl

theorem eval_rename (A : Algebra S) (ν : Valuation A.Carrier)
    {k l : Nat} (t : Term S k) (ρ : Fin k → Fin l) (env : Fin l → A.Carrier) :
    (t.rename ρ).eval A ν env = t.eval A ν (env ∘ ρ) := by
  induction t generalizing l with
  | bound => rfl
  | free x args ih => exact congrArg (ν _ x) (funext fun i => ih i ρ env)
  | app a args ih =>
    simp only [Term.rename, Term.eval]
    apply congrArg (A.op a)
    funext i values
    rw [ih]
    apply congrArg ((args i).eval A ν)
    funext j
    refine Fin.addCases (fun left => ?_) (fun right => ?_) j
    · simp only [Function.comp_apply, Fin.addCases_left]
    · simp only [Function.comp_apply, Fin.addCases_right]

theorem eval_instantiate (A : Algebra S) (ν : Valuation A.Carrier)
    {k l : Nat} (t : Term S k) (σ : Fin k → Term S l) (env : Fin l → A.Carrier) :
    (t.instantiate σ).eval A ν env = t.eval A ν (fun i => (σ i).eval A ν env) := by
  induction t generalizing l with
  | bound => rfl
  | free x args ih => exact congrArg (ν _ x) (funext fun i => ih i σ env)
  | app a args ih =>
    simp only [Term.instantiate, Term.eval]
    apply congrArg (A.op a)
    funext i values
    rw [ih]
    apply congrArg ((args i).eval A ν)
    funext j
    refine Fin.addCases (fun left => ?_) (fun right => ?_) j
    · simp only [Fin.addCases_left, eval_rename]
      apply congrArg ((σ _).eval A ν)
      funext index
      simp only [Function.comp_apply, Fin.addCases_left]
    · simp only [Fin.addCases_right, Term.eval]

theorem eval_subst (A : Algebra S) (ν : Valuation A.Carrier) (σ : Substitution S)
    {k : Nat} (t : Term S k) (env : Fin k → A.Carrier) :
    (t.subst σ).eval A ν env = t.eval A (A.substValuation ν σ) env := by
  induction t with
  | bound => rfl
  | @free k n x args ih =>
    cases h : σ n x <;>
      simp only [Term.subst, Term.eval, Algebra.substValuation, h, eval_instantiate, ih]
  | app a args ih =>
    exact congrArg (A.op a) (funext fun i => funext fun values =>
      ih i (Fin.addCases env values))

theorem holdsAt_subst (A : Algebra S) (O : LogicalOrder A.Carrier) (ν : Valuation A.Carrier)
    (σ : Substitution S) (r : Rule S) :
    (r.subst σ).HoldsAt A O ν ↔ r.HoldsAt A O (A.substValuation ν σ) := by
  simp only [Rule.HoldsAt, Rule.subst, List.forall_mem_map, Premise.subst, eval_subst]

end Silmaril.Proofs.Logic.Abstraction
