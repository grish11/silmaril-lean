module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Syntax.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Hom
open CategoryTheory Silmaril.Logic.Algebraic
variable {A B C : Signature}

theorem value_heq (f : A ⟶ B) (M : Model B.symbols) (s : SortCode A.users)
    (x : (carriers f M).value s) : HEq (value f M s x) x := by
  exact cast_heq _ _

theorem value_symm_heq (f : A ⟶ B) (M : Model B.symbols) (s : SortCode A.users)
    (x : M.carriers.value (f.sorts s)) : HEq ((value f M s).symm x) x := by
  exact cast_heq _ _

theorem reduct_id (M : Model A.symbols) : reduct (𝟙 A) M = M := by
  cases M
  rfl

private theorem apply_heq (M : Model B.symbols) {n : Nat}
    {ss tt : Fin n → SortCode B.users} {s t : SortCode B.users}
    (hss : ss = tt) (hs : s = t)
    (op : Operation B.symbols n ss s) (op' : Operation B.symbols n tt t)
    (hop : HEq op op') (args : ∀ i, M.carriers.value (ss i))
    (args' : ∀ i, M.carriers.value (tt i))
    (hargs : ∀ i, HEq (args i) (args' i)) :
    HEq (M.apply op args) (M.apply op' args') := by
  cases hss
  cases hs
  cases eq_of_heq hop
  have same : args = args' := funext (fun i => eq_of_heq (hargs i))
  cases same
  rfl

theorem apply_operation (f : A ⟶ B) (M : Model B.symbols)
    {n inputs output} (op : Operation A.symbols n inputs output)
    (args : (i : Fin n) → (carriers f M).value (inputs i)) :
    value f M output ((reduct f M).apply op args) =
      M.apply (operation f op) (fun i => value f M (inputs i) (args i)) := by
  classical
  cases op with
  | uf symbol => exact (value f M _).apply_symm_apply _
  | boolean b =>
      apply eq_of_heq
      refine (value_heq f M .bool b).trans ?_
      symm
      exact apply_heq M (sorts_empty f) f.bool _ (.boolean b)
        (by unfold operation; exact cast_heq _ _)
        _ (fun i => i.elim0) (fun i => i.elim0)
  | integer b =>
      apply eq_of_heq
      refine (value_heq f M .int b).trans ?_
      symm
      exact apply_heq M (sorts_empty f) f.int _ (.integer b)
        (by unfold operation; exact cast_heq _ _)
        _ (fun i => i.elim0) (fun i => i.elim0)
  | add =>
      apply eq_of_heq
      refine (value_heq f M .int ((reduct f M).apply (.add) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.int)) f.int _ (.add)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .int (args i))
  | sub =>
      apply eq_of_heq
      refine (value_heq f M .int ((reduct f M).apply (.sub) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.int)) f.int _ (.sub)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .int (args i))
  | scale c =>
      apply eq_of_heq
      refine (value_heq f M .int ((reduct f M).apply (.scale c) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.int)) f.int _ (.scale c)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .int (args i))
  | le =>
      apply eq_of_heq
      refine (value_heq f M .bool ((reduct f M).apply (.le) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.int)) f.bool _ (.le)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .int (args i))
  | lt =>
      apply eq_of_heq
      refine (value_heq f M .bool ((reduct f M).apply (.lt) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.int)) f.bool _ (.lt)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .int (args i))
  | not =>
      apply eq_of_heq
      refine (value_heq f M .bool ((reduct f M).apply (.not) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.bool)) f.bool _ (.not)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .bool (args i))
  | and =>
      apply eq_of_heq
      refine (value_heq f M .bool ((reduct f M).apply (.and) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.bool)) f.bool _ (.and)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .bool (args i))
  | or =>
      apply eq_of_heq
      refine (value_heq f M .bool ((reduct f M).apply (.or) args)).trans ?_
      symm
      exact apply_heq M (funext (fun _ => f.bool)) f.bool _ (.or)
        (by unfold operation; exact cast_heq _ _)
        _ args (fun i => value_heq f M .bool (args i))
  | eq s =>
      apply eq_of_heq
      refine (value_heq f M .bool ((reduct f M).apply (.eq s) args)).trans ?_
      have htarget := apply_heq M rfl f.bool (operation f (.eq s)) (.eq (f.sorts s))
        (by unfold operation; exact cast_heq _ _)
        (fun i => value f M s (args i)) (fun i => value f M s (args i))
        (fun _ => HEq.rfl)
      apply HEq.trans (c := _) ?_ htarget.symm
      apply heq_of_eq
      change decide (args 0 = args 1) = decide (value f M s (args 0) = value f M s (args 1))
      exact congrArg (fun p : Prop => decide p) (propext (value f M s).injective.eq_iff.symm)
  | ite _ =>
      apply eq_of_heq
      have profiles : f.sorts ∘ Fin.cases .bool (fun _ : Fin 2 => output) =
          Fin.cases .bool (fun _ : Fin 2 => f.sorts output) := by
        funext i
        exact Fin.cases f.bool (fun _ => rfl) i
      let targetArgs : (i : Fin 3) → M.carriers.value
          (Fin.cases .bool (fun _ : Fin 2 => f.sorts output) i) :=
        Fin.cases (args 0) (fun i => value f M output (args i.succ))
      have hargs (i : Fin 3) :
          HEq (value f M (Fin.cases .bool (fun _ : Fin 2 => output) i) (args i)) (targetArgs i) := by
        cases i using Fin.cases with
        | zero => exact value_heq f M .bool (args 0)
        | succ i => rfl
      have htarget := apply_heq M profiles rfl (operation f (.ite output)) (.ite (f.sorts output))
        (by
          have shifted : operation f (.ite output) =
              profiles.symm ▸ (Operation.ite (A := B.symbols) (f.sorts output)) := by
            cases output <;> rfl
          rw [shifted]
          exact eqRec_heq (φ := fun ss : Fin 3 → SortCode B.users =>
            Operation B.symbols 3 ss (f.sorts output)) profiles.symm (.ite (f.sorts output)))
        _ targetArgs hargs
      apply HEq.trans (c := _) ?_ htarget.symm
      apply heq_of_eq
      change value f M output (if args 0 = true then args 1 else args 2) =
        (if args 0 = true then value f M output (args 1) else value f M output (args 2))
      by_cases h : args 0 = true <;> simp [h]

/-- Open evaluation commutes with sort and symbol transport. -/
theorem eval_term (f : A ⟶ B) (M : Model B.symbols) {k : Nat}
    {Γ : Fin k → SortCode A.users} {s : SortCode A.users}
    (t : ManySorted.Term A.symbols.expanded Γ s)
    (values : ∀ i, (carriers f M).value (Γ i)) :
    value f M s ((reduct f M).algebra.eval values t) =
      M.algebra.eval (fun i => value f M (Γ i) (values i)) (term f t) := by
  induction t with
  | var i => rfl
  | app op args ih =>
      exact (apply_operation f M op
        (fun i => (reduct f M).algebra.eval values (args i))).trans
          (congrArg (M.apply (operation f op)) (funext ih))

private theorem eval_heq (M : Model B.symbols) {k : Nat}
    {Γ Δ : Fin k → SortCode B.users} {s t : SortCode B.users}
    (hΓ : Γ = Δ) (hs : s = t)
    (p : ManySorted.Term B.symbols.expanded Γ s)
    (q : ManySorted.Term B.symbols.expanded Δ t) (hp : HEq p q)
    (v : ∀ i, M.carriers.value (Γ i)) (w : ∀ i, M.carriers.value (Δ i))
    (hv : ∀ i, HEq (v i) (w i)) : HEq (M.algebra.eval v p) (M.algebra.eval w q) := by
  cases hΓ
  cases hs
  cases eq_of_heq hp
  have same : v = w := funext (fun i => eq_of_heq (hv i))
  cases same
  rfl

theorem formula_heq (f : A ⟶ B) (p : Formula A.symbols) :
    HEq (formula f p) (term f p) := by
  unfold formula
  exact (cast_heq _ _).trans (cast_heq _ _)

theorem holds_formula (f : A ⟶ B) (M : Model B.symbols) (p : Formula A.symbols) :
    M.Holds (formula f p) ↔ (reduct f M).Holds p := by
  have ev := eval_term f M p (fun i => i.elim0)
  have shifted := eval_heq M (sorts_empty f).symm f.bool.symm (formula f p) (term f p)
    (formula_heq f p) (fun i => i.elim0) (fun i => (value f M (Fin.elim0 i)).toFun (i.elim0))
    (fun i => i.elim0)
  have same : M.eval (formula f p) = (reduct f M).eval p := by
    apply eq_of_heq
    exact shifted.trans ((heq_of_eq ev.symm).trans (value_heq f M .bool _))
  exact iff_of_eq (congrArg (fun b : Bool => b = true) same)

end Silmaril.Logic.Smt.Uflia.SortMaps.Hom
