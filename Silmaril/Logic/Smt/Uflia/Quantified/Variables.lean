module

public import Silmaril.Logic.Smt.Uflia.Quantified.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified
variable {U : Type} {A : Signature U}

/-- A typed reference packages its index with its sort by construction. -/
inductive Ref {k : Nat} (Γ : Fin k → SortCode U) : SortCode U → Type where
  | index (i : Fin k) : Ref Γ (Γ i)

def Ref.succ {l : Nat} {Δ : Fin l → SortCode U} {s : SortCode U}
    (sort : SortCode U) : Ref Δ s → Ref (Fin.cases sort Δ) s
  | .index i => .index i.succ

def Ref.term {l : Nat} {Δ : Fin l → SortCode U} {s : SortCode U} :
    Ref Δ s → Term A Δ s
  | .index i => .var i

def Ref.lift {k l : Nat} {Γ : Fin k → SortCode U} {Δ : Fin l → SortCode U}
    (r : ∀ i, Ref Δ (Γ i)) (sort : SortCode U) :
    ∀ i, Ref (Fin.cases sort Δ) ((Fin.cases sort Γ : Fin (k + 1) → SortCode U) i) :=
  Fin.cases (motive := fun i => Ref (Fin.cases sort Δ) ((Fin.cases sort Γ : Fin (k + 1) → SortCode U) i))
    (.index 0) (fun i => Ref.succ sort (r i))

/-- Capture-avoiding variable renaming lifts under every nested quantifier. -/
def Term.rename : {k l : Nat} → {Γ : Fin k → SortCode U} → {Δ : Fin l → SortCode U} →
    (∀ i, Ref Δ (Γ i)) → {s : SortCode U} → Term A Γ s → Term A Δ s := by
  intro k l Γ Δ r s t
  exact match t with
  | .var i => Ref.term (r i)
  | .app op args => .app op (fun i => Term.rename r (args i))
  | .all sort body => .all sort (Term.rename (Ref.lift r sort) body)
  | .ex sort body => .ex sort (Term.rename (Ref.lift r sort) body)

def Term.weaken {k : Nat} {Γ : Fin k → SortCode U} {s : SortCode U}
    (sort : SortCode U) (t : Term A Γ s) : Term A (Fin.cases sort Γ) s :=
  t.rename (fun i => Ref.index i.succ)

def Ref.value (M : Model A) {l : Nat} {Δ : Fin l → SortCode U}
    (values : ∀ i, M.carriers.value (Δ i)) {s} : Ref Δ s → M.carriers.value s
  | .index i => values i

theorem Ref.eval_term (M : Model A) {l : Nat} {Δ : Fin l → SortCode U}
    (values : ∀ i, M.carriers.value (Δ i)) {s} (r : Ref Δ s) :
    eval M values r.term = Ref.value M values r := by
  cases r
  rfl

theorem Ref.value_succ (M : Model A) {l : Nat} {Δ : Fin l → SortCode U}
    (values : ∀ i, M.carriers.value (Δ i)) {s} (r : Ref Δ s)
    (sort : SortCode U) (x : M.carriers.value sort) :
    Ref.value M (Fin.cases x values) (r.succ sort) = Ref.value M values r := by
  cases r
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem eval_rename (M : Model A) {k Γ s} (t : Term A (k := k) Γ s) :
    ∀ {l : Nat} {Δ : Fin l → SortCode U} (r : ∀ i, Ref Δ (Γ i))
      (values : ∀ i, M.carriers.value (Δ i)),
    eval M values (t.rename r) = eval M (fun i => Ref.value M values (r i)) t := by
  classical
  induction t with
  | var i =>
      intro l Δ r values
      exact Ref.eval_term M values (r i)
  | app op args ih =>
      intro l Δ r values
      change M.apply op (fun i => eval M values ((args i).rename r)) = _
      simp only [ih]
      rfl
  | all sort body ih =>
      intro l Δ r values
      change decide (∀ x : M.carriers.value sort,
        eval M (Fin.cases x values) (body.rename (Ref.lift r sort)) = true) =
        decide (∀ x : M.carriers.value sort,
          eval M (Fin.cases x (fun i => Ref.value M values (r i))) body = true)
      congr 1
      apply propext
      have h (x : M.carriers.value sort) :
          (fun i => Ref.value M (Fin.cases x values) (Ref.lift r sort i)) =
            Fin.cases x (fun i => Ref.value M values (r i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact Ref.value_succ M values (r j) sort x
      simp only [ih, h]
  | ex sort body ih =>
      intro l Δ r values
      change decide (∃ x : M.carriers.value sort,
        eval M (Fin.cases x values) (body.rename (Ref.lift r sort)) = true) =
        decide (∃ x : M.carriers.value sort,
          eval M (Fin.cases x (fun i => Ref.value M values (r i))) body = true)
      congr 1
      apply propext
      have h (x : M.carriers.value sort) :
          (fun i => Ref.value M (Fin.cases x values) (Ref.lift r sort i)) =
            Fin.cases x (fun i => Ref.value M values (r i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact Ref.value_succ M values (r j) sort x
      simp only [ih, h]

set_option backward.isDefEq.respectTransparency false in
theorem eval_weaken (M : Model A) {k Γ s} (t : Term A (k := k) Γ s)
    (sort : SortCode U) (values : ∀ i, M.carriers.value (Γ i))
    (x : M.carriers.value sort) :
    eval M (Fin.cases x values) (t.weaken sort) = eval M values t := by
  rw [Term.weaken, eval_rename]
  rfl

end Silmaril.Logic.Smt.Uflia.Quantified
