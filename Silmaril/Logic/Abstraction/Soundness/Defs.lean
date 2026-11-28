module

public import Silmaril.Logic.Abstraction.Defs

@[expose] public section

/-!
# The rule calculus of Abstraction Logic

Obua, *Abstraction Logic: A Complete Logic over Second-Order Abstract Syntax*, Figure 4
(`obua-2026-abstraction-logic-primer` in `references.bib`). Antecedents are sets, as in the
Primer. The public institutional sentences supply finite list representatives. The seven
constructors generate only finite antecedents. Well-formedness and bound-name renaming
are handled by the scopes of `Term`. Each argument uses the parameter count of its
declared scope, with the full shape retained in the symbol's type.

To recover a named outer template, open its local parameters with distinct names that
are absent from its free nullary occurrences. For Bind, the two openings must give the
same body, and the old names missing from the new binder list must be absent from that
body. This permits permutation, addition (including capture of a formerly free nullary
name), and removal of unused binders in a single step. Infer uses the same opening for
the supplying conclusion. Only the supplying premises must be fresh for the opened
names. Occurrences at positive arity are independent of the nullary names.
-/

namespace Silmaril.Logic.Abstraction

variable {S : Signature}

/-- Absence of a free occurrence at arity zero, including inside abstraction arguments. -/
def Term.Fresh (x : Nat) : {k : Nat} → Term S k → Prop
  | _, .bound _ => True
  | _, .free (n := 0) y _ => x ≠ y
  | _, .free (n := _ + 1) _ args => ∀ i, (args i).Fresh x
  | _, .app _ args => ∀ i, (args i).Fresh x

/-- Expose the outer parameters as the given nullary names. For a faithful opening, use
distinct names fresh for the template's free nullary occurrences. -/
def Term.openWith : {k : Nat} → Template S k → (Fin k → Nat) → Term S 0
  | 0, t, _ => t
  | _ + 1, t, names => t.instantiate (fun i => Term.var (names i))

/-- Finite rule hypotheses, viewed as a set for the structural operations of the calculus. -/
def Rule.antecedent (r : Rule S) : Set (Premise S) := {p | p ∈ r.premises}

/-- Derivations from a set of theory axioms. Object-language rules (for example, rules for a
universal abstraction) enter through `axiom`, just like any other rule of the theory. -/
inductive Derives (theory : Set (Rule S)) : Set (Premise S) → Term S 0 → Prop
  | axiom {r : Rule S} : r ∈ theory → Derives theory r.antecedent r.conclusion
  | assume (t : Term S 0) : Derives theory {⟨0, t⟩} t
  | add {Γ : Set (Premise S)} {t : Term S 0} (p : Premise S) :
      Derives theory Γ t → Derives theory (insert p Γ) t
  | bind {Γ : Set (Premise S)} {t : Term S 0} {k l : Nat}
      {p : Template S k} {q : Template S l}
      (oldNames : Fin k ↪ Nat) (newNames : Fin l ↪ Nat) :
      (∀ i, p.Fresh (oldNames i)) →
      (∀ j, q.Fresh (newNames j)) →
      p.openWith oldNames = q.openWith newNames →
      (∀ i, oldNames i ∉ Set.range newNames → (p.openWith oldNames).Fresh (oldNames i)) →
      Derives theory (insert ⟨k, p⟩ Γ) t →
      Derives theory (insert ⟨l, q⟩ Γ) t
  | subst {Γ : Set (Premise S)} {t : Term S 0} (σ : Substitution S) :
      Derives theory Γ t → Derives theory (Premise.subst σ '' Γ) (t.subst σ)
  | varElim {Γ : Set (Premise S)} {t : Term S 0} (x : Nat) :
      (∀ p ∈ Γ, p.2.Fresh x) → t.Fresh x →
      Derives theory (insert ⟨0, Term.var x⟩ Γ) t → Derives theory Γ t
  | infer {Γ Δ : Set (Premise S)} {t : Term S 0} {k : Nat} {p : Template S k}
      (names : Fin k ↪ Nat) :
      (∀ i, p.Fresh (names i)) →
      (∀ q ∈ Δ, ∀ i, q.2.Fresh (names i)) →
      Derives theory (insert ⟨k, p⟩ Γ) t →
      Derives theory Δ (p.openWith names) →
      Derives theory (Γ ∪ Δ) t

/-- Derivability for the institution's list-presented sentences. -/
abbrev Rule.Derivable (r : Rule S) (theory : Set (Rule S)) : Prop :=
  Derives theory r.antecedent r.conclusion

end Silmaril.Logic.Abstraction
