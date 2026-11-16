module

public import Silmaril.Logic.CommonLogic.ManySorted.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.CommonLogic.ManySorted

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic
open Silmaril.Logic.CommonLogic.ManySorted

/-- Finite tuples evaluate in their declared order, including arity zero. -/
theorem tuple_eval {S : Core.Signature} {n k m : Nat} (M : Core.Model S)
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (args : Fin m → Core.Expr S n k .individual) :
    (tuple args).eval M ρ σ = List.ofFn (fun i => (args i).eval M ρ σ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (args 0).eval M ρ σ :: (tuple (fun i => args i.succ)).eval M ρ σ = _
    rw [List.ofFn_succ, ih]

theorem tuple_map {S T : Core.Signature} (f : S ⟶ T) {n k m : Nat}
    (args : Fin m → Core.Expr S n k .individual) :
    (tuple args).map f = tuple (fun i => (args i).map f) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg₂ Core.Expr.cons rfl (ih _)

theorem guards_holds {S : FOL.Signature} {n k m : Nat} (M : Core.Model (signature S))
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (w : Fin m → S.S) (ts : Fin m → Core.Expr (signature S) n k .individual) :
    (guards w ts).Holds M ρ σ ↔
      ∀ i, M.relation (M.nondiscourse (.sort (w i))) [(ts i).eval M ρ σ] := by
  induction m with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => True.intro⟩
  | succ m ih =>
    change (M.relation (M.nondiscourse (.sort (w 0))) [(ts 0).eval M ρ σ] ∧
      (guards (fun i => w i.succ) (fun i => ts i.succ)).Holds M ρ σ) ↔ _
    rw [ih]
    constructor
    · intro h i
      exact Fin.cases h.1 h.2 i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem close_holds {S : Core.Signature} (M : Core.Model S) :
    {n : Nat} → (p : Core.Formula S n 0) →
    (close p).Holds M Fin.elim0 Fin.elim0 ↔ ∀ ρ, p.Holds M ρ Fin.elim0
  | 0, p => by
    constructor
    · intro h ρ
      have heq : ρ = Fin.elim0 := funext (fun i => Fin.elim0 i)
      simpa only [close, heq] using h
    · intro h
      exact h Fin.elim0
  | n+1, p => by
    change (close (.all p)).Holds M Fin.elim0 Fin.elim0 ↔ _
    rw [close_holds M (.all p)]
    constructor
    · intro h ρ
      have heq : Fin.cases (ρ 0) (fun i => ρ i.succ) = ρ := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simpa only [heq] using h (fun i => ρ i.succ) (ρ 0)
    · intro h ρ x
      exact h (Fin.cases x ρ)

/-- The syntactic theory is exactly the closure condition used by the decoder. -/
theorem wellTyped_iff {S : FOL.Signature} (M : Core.Model (signature S)) :
    WellTyped M ↔ ∀ p ∈ typingTheory S, p.Holds M Fin.elim0 Fin.elim0 := by
  have hax : ∀ {n : Nat} {w : Fin n → S.S} {s : S.S} (o : S.Op n w s),
      (typingAxiom o).Holds M Fin.elim0 Fin.elim0 ↔
      ∀ xs : Fin n → M.Discourse,
        (∀ i, M.relation (M.nondiscourse (.sort (w i))) [xs i]) →
        M.relation (M.nondiscourse (.sort s))
          [M.function (M.nondiscourse (.op o)) (List.ofFn xs)] := by
    intro n w s o
    unfold typingAxiom
    rw [close_holds]
    simp only [Core.Formula.Holds, guards_holds,
      Silmaril.Logic.CommonLogic.ManySorted.guard, Core.Expr.eval, tuple_eval]
  constructor
  · intro h p hp
    obtain ⟨n, w, s, o, rfl⟩ := hp
    exact (hax o).mpr (h o)
  · intro h n w s o
    exact (hax o).mp (h (typingAxiom o) ⟨n, w, s, o, rfl⟩)

theorem term_map {S T : FOL.Signature} (f : S ⟶ T) {n k : Nat} {Γ : Fin n → S.S} :
    {s : S.S} → (t : EQ.Term S.toSignature Γ s) →
    (term (k := k) t).map (signatureMap f) = term (t.map f.toHom)
  | _, .var _ => rfl
  | _, .app o args => by
    dsimp only [term, Core.Expr.map, EQ.Term.map]
    rw [tuple_map]
    exact congrArg (Core.Expr.app _) (congrArg tuple (funext fun i => term_map f (args i)))

theorem formula_map {S T : FOL.Signature} (f : S ⟶ T) :
    {n k : Nat} → {Γ : Fin n → S.S} → (p : FOL.Formula S Γ) →
    (formula (k := k) p).map (signatureMap f) = formula (p.map f)
  | _, _, _, .eq t u => congrArg₂ Core.Formula.equal (term_map f t) (term_map f u)
  | _, _, _, .rel r args => by
    dsimp only [formula, Core.Formula.map, Core.Expr.map, FOL.Formula.map]
    rw [tuple_map]
    exact congrArg (Core.Formula.pred _) (congrArg tuple (funext fun i => term_map f (args i)))
  | _, _, _, .tt => rfl
  | _, _, _, .not p => congrArg Core.Formula.neg (formula_map f p)
  | _, _, _, .and p q => congrArg₂ Core.Formula.conj (formula_map f p) (formula_map f q)
  | _, _, _, .all _ p =>
      congrArg Core.Formula.all (congrArg (Core.Formula.impl _) (formula_map f p))

/-- The dependent public assignment convention agrees with first-variable binding. -/
theorem assignment_eq {n : Nat} {D : Fin (n+1) → Type}
    (ρ : ∀ i : Fin n, D i.succ) (ρ' : ∀ i, D i)
    (h : ∀ i, HEq (ρ' i.succ) (ρ i)) : ρ' = Fin.cases (ρ' 0) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact eq_of_heq (h j)

/-- Projecting a dependent subtype assignment commutes with first-variable extension. -/
theorem project_cases {S : FOL.Signature} {n : Nat} (M : TypedModel S)
    (Δ : Fin (n+1) → S.S) (x : (decode M).carrier (Δ 0))
    (ρ : ∀ i : Fin n, (decode M).carrier (Δ i.succ)) :
    (fun i => (Fin.cases (motive := fun j => (decode M).carrier (Δ j)) x ρ i).val) =
      Fin.cases x.val (fun i => (ρ i).val) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem term_eval {S : FOL.Signature} {n k : Nat} {Γ : Fin n → S.S}
    (M : TypedModel S) (ρ : ∀ i, (decode M).carrier (Γ i))
    (σ : Fin k → List M.obj.Discourse) :
    {s : S.S} → (t : EQ.Term S.toSignature Γ s) →
    (term t).eval M.obj (fun i => (ρ i).val) σ = (t.eval (decode M).toAlgebra ρ).val
  | _, .var _ => rfl
  | _, .app o args => by
    simp only [term, Core.Expr.eval]
    rw [tuple_eval]
    exact congrArg (M.obj.function _) (congrArg List.ofFn
      (funext fun i => term_eval M ρ σ (args i)))

/-- Satisfaction is preserved for all sorted assignments, with no carrier inhabitants assumed. -/
theorem formula_holds {S : FOL.Signature} (M : TypedModel S) :
    {n k : Nat} → {Γ : Fin n → S.S} → (p : FOL.Formula S Γ) →
    (ρ : ∀ i, (decode M).carrier (Γ i)) → (σ : Fin k → List M.obj.Discourse) →
    p.Holds (decode M) ρ ↔ (formula p).Holds M.obj (fun i => (ρ i).val) σ
  | _, _, _, .eq t u, ρ, σ => by
    change t.eval (decode M).toAlgebra ρ = u.eval (decode M).toAlgebra ρ ↔
      (term t).eval M.obj (fun i => (ρ i).val) σ =
        (term u).eval M.obj (fun i => (ρ i).val) σ
    rw [term_eval, term_eval]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  | _, _, _, .rel r args, ρ, σ => by
    dsimp only [formula, Core.Formula.Holds, Core.Expr.eval]
    rw [tuple_eval]
    exact (congrArg (M.obj.relation _) (congrArg List.ofFn
      (funext fun i => term_eval M ρ σ (args i)))).symm.to_iff
  | _, _, _, .tt, _, _ => Iff.rfl
  | _, _, _, .not p, ρ, σ => not_congr (formula_holds M p ρ σ)
  | _, _, _, .and p q, ρ, σ => and_congr (formula_holds M p ρ σ) (formula_holds M q ρ σ)
  | _, _, _, .all (Δ := Δ) h p, ρ, σ => by
    cases h
    change (∀ ρ', (∀ i, HEq (ρ' i.succ) (ρ i)) → p.Holds (decode M) ρ') ↔
      ∀ x, M.obj.relation (M.obj.nondiscourse (.sort (Δ 0))) [x] →
        (formula p).Holds M.obj (Fin.cases x (fun i => (ρ i).val)) σ
    constructor
    · intro hall x hx
      have hh := (formula_holds M p (Fin.cases ⟨x, hx⟩ ρ) σ).mp
        (hall (Fin.cases ⟨x, hx⟩ ρ) (fun _ => HEq.rfl))
      simpa only [project_cases] using hh
    · intro hall ρ' hagree
      have heq := assignment_eq ρ ρ' hagree
      rw [heq]
      apply (formula_holds M p (Fin.cases (ρ' 0) ρ) σ).mpr
      simpa only [project_cases] using hall (ρ' 0).val (ρ' 0).property

end Silmaril.Proofs.Logic.CommonLogic.ManySorted
