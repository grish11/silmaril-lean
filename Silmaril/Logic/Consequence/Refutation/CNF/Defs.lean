module

public import Silmaril.Logic.Consequence.Refutation.Defs
public import Silmaril.Logic.SAT.CNF.Defs

/-!
# Clause entailment by CNF refutation

Instantiates `Silmaril.Logic.Consequence.Refutation` with the DIMACS syntax of
`Silmaril.Logic.SAT` (`Lit := Int`, `Clause := List Lit`, `CNF := List Clause`):

* formulas are clauses without the literal `0` (`WClause`). `0` is the DIMACS terminator,
  and `-0 = 0`, so negating a literal complements its value only for nonzero literals;
* `csat τ C`: the assignment `τ` satisfies the clause `C` (`Clause.eval`);
* `cneg C`: the unit clauses `[-l]` for `l ∈ C`, the CNF of the negation of `C`. It is
  exact (`NegSound` and `NegComplete`, in `…CNF.Thms`);
* `Tauto C`: `C` contains a complementary pair `l, -l` (decidable).

`…CNF.Thms` proves that a list `Γ` of clauses entails `C` iff the CNF
`Γ ++ cneg C` is `CNF.Unsat`, and that `[]` entails `C` iff `Tauto C`.
-/

@[expose] public section

namespace Silmaril.Consequence.Refutation.CNF

open Silmaril.Logic.SAT

/-- A clause without the DIMACS terminator `0`. -/
abbrev WClause := { C : Clause // (0 : Lit) ∉ C }

/-- An assignment satisfies a clause. -/
def csat (τ : Assignment) (C : WClause) : Prop := C.1.eval τ = true

/-- The negation of a clause: the unit clauses of its negated literals. -/
def cneg (C : WClause) : List WClause :=
  C.1.attach.map fun l => ⟨[-l.1], by
    simp only [List.mem_singleton]
    intro h
    have h0 : (l.1 : Int) = 0 := by simpa using h.symm
    exact C.2 (by have := l.2; rwa [h0] at this)⟩

/-- The clauses underlying a list of `WClause`s, as a CNF formula. -/
def toCNF (Γ : List WClause) : CNF := Γ.map Subtype.val

/-- A clause is a tautology: it contains a literal and its negation. -/
def Tauto (C : Clause) : Prop := ∃ l ∈ C, -l ∈ C

instance (C : Clause) : Decidable (Tauto C) := inferInstanceAs (Decidable (∃ l ∈ C, -l ∈ C))

end Silmaril.Consequence.Refutation.CNF
