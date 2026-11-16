module

public import Silmaril.Logic.Smt.Uflia.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified
open CategoryTheory Silmaril.Inst Silmaril.Logic.Algebraic
variable {U : Type}

/-- A single sorted syntax admits quantified Boolean terms in every Boolean
term position, including UF arguments, equality operands and ite guards. -/
inductive Term (A : Signature U) : {k : Nat} → (Fin k → SortCode U) → SortCode U → Type where
  | var {k Γ} (i : Fin k) : Term A Γ (Γ i)
  | app {k Γ n inputs output} (op : Operation A n inputs output)
      (args : (i : Fin n) → Term A (k := k) Γ (inputs i)) : Term A Γ output
  | all {k Γ} (sort : SortCode U) :
      Term A (k := k + 1) (Fin.cases sort Γ) .bool → Term A (k := k) Γ .bool
  | ex {k Γ} (sort : SortCode U) :
      Term A (k := k + 1) (Fin.cases sort Γ) .bool → Term A (k := k) Γ .bool

abbrev Formula (A : Signature U) {k : Nat} (Γ : Fin k → SortCode U) := Term A Γ .bool
abbrev Sentence (A : Signature U) := Formula A (fun i : Fin 0 => i.elim0)

/-- Quantifiers range over actual standard Bool/Int or nonempty user carriers.
Their Boolean values are classical truth values, not finite enumerations. -/
noncomputable def eval {A : Signature U} (M : Model A) :
    {k : Nat} → {Γ : Fin k → SortCode U} → {s : SortCode U} →
    ((i : Fin k) → M.carriers.value (Γ i)) → Term A Γ s → M.carriers.value s := by
  classical
  intro k Γ s values t
  exact match t with
  | .var i => values i
  | .app op args => M.apply op (fun i => eval M values (args i))
  | .all sort body => decide (∀ x : M.carriers.value sort,
      eval M (Fin.cases x values) body = true)
  | .ex sort body => decide (∃ x : M.carriers.value sort,
      eval M (Fin.cases x values) body = true)

noncomputable def Formula.Holds {A : Signature U} {k : Nat} {Γ : Fin k → SortCode U}
    (p : Formula A Γ)
    (M : Model A) (values : ∀ i, M.carriers.value (Γ i)) : Prop := eval M values p = true
noncomputable def Sentence.Holds {A : Signature U} (p : Sentence A) (M : Model A) : Prop :=
  Formula.Holds p M (fun i => i.elim0)
noncomputable def Sentence.Sat {A : Signature U} (p : Sentence A) : Prop := ∃ M, p.Holds M
noncomputable def Sentence.Unsat {A : Signature U} (p : Sentence A) : Prop := ¬ p.Sat

/-- Embed existing open sorted core terms; ground APIs themselves are unchanged. -/
def Term.ofCore {A : Signature U} {k Γ s} : ManySorted.Term A.expanded (k := k) Γ s → Term A Γ s
  | .var i => .var i
  | .app op args => .app op (fun i => ofCore (args i))

def ground {A : Signature U} (p : Uflia.Formula A) : Sentence A := Term.ofCore p

def Term.map {A B : Signature U} (f : A ⟶ B) :
    {k : Nat} → {Γ : Fin k → SortCode U} → {s : SortCode U} → Term A Γ s → Term B Γ s := by
  intro k Γ s t
  exact match t with
  | .var i => .var i
  | .app op args => .app (Operation.map f op) (fun i => Term.map f (args i))
  | .all sort body => .all sort (Term.map f body)
  | .ex sort body => .ex sort (Term.map f body)

end Silmaril.Logic.Smt.Uflia.Quantified
