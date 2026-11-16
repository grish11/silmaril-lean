module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Defs
public import Silmaril.Logic.SAT.CNF.Defs
public import Silmaril.Logic.SAT.LRAT.Defs

/-!
# Clausal acceptors over DIMACS, and the DIMACS image of signed clauses

**DIMACS as a CNF acceptor carrier.** `Silmaril.Logic.SAT` has DIMACS literals `Lit := Int`,
clauses and formulas (`SAT.CNF := List (List Int)`) and the reader `Dimacs.read`; `0` is the
clause terminator, not a literal. `litSat τ l` (`Lit.eval τ l = true`) is the satisfaction of
DIMACS literals by assignments `Nat → Bool`, so `CnfUnsat litSat` is `SAT.CNF.Unsat`
(`…Dimacs.Thms`). `lratAccepts F` (some proof passes the reference checker `LRAT.check`) is a
CNF acceptor; it is *sound* (`LRAT.check_sound`), and nothing about its closure or
completeness is claimed.

**The DIMACS image of signed clauses.** For clauses over `Signed A`, an explicit variable map
`v : A → Nat` gives `encLit v (pos a) = v a` and `encLit v (neg a) = -(v a)`, and
`encode v F` maps every literal. `atoms F` is the finite support of `F` (its atoms, with
repetitions). `Coherent v F` is what the transfer needs on that support:

* `nonzero`: `v a ≠ 0`, so no literal is the terminator `0` (which is also its own negation);
* `injOn`: distinct atoms get distinct variables (no collision), so `pos a` and `neg b` are
  complementary DIMACS literals only when `a = b`.

The sign flip always commutes with `encLit` (`encLit_neg`); coherence is what makes integer
negation a *semantic* complement on the image. The transfer is one-directional:
source satisfiable ⇒ image satisfiable, hence image UNSAT ⇒ source UNSAT. It assumes that the
source satisfaction reads `neg a` as excluding `pos a` (`Gentzen.NegSound`, true for
`signedSat`), and it is stated for every model type `M` (satisfiability is relative to `M`).
The converse fails for restricted model types (`…Dimacs.Examples`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Clausal

open Silmaril.Logic.SAT

universe u

/-- A DIMACS literal holds under an assignment. -/
def litSat (τ : Assignment) (l : Lit) : Prop := l.eval τ = true

/-- Some LRAT proof of `F` passes the reference checker. -/
def lratAccepts (F : Silmaril.Logic.SAT.CNF) : Prop := ∃ proof, LRAT.check F proof = true

variable {A : Type u}

/-- The DIMACS literal of a signed atom, along the variable map `v`. -/
def encLit (v : A → Nat) : Signed A → Lit
  | .pos a => (v a : Int)
  | .neg a => -(v a : Int)

/-- The DIMACS image of a CNF formula over signed atoms. -/
def encode (v : A → Nat) (F : List (List (Signed A))) : Silmaril.Logic.SAT.CNF :=
  F.map (List.map (encLit v))

/-- The atoms of a formula: its finite support. -/
def atoms (F : List (List (Signed A))) : List A := F.flatMap (List.map Signed.atom)

/-- The variable map is nonzero and injective on the support of `F`. -/
structure Coherent (v : A → Nat) (F : List (List (Signed A))) : Prop where
  nonzero : ∀ a ∈ atoms F, v a ≠ 0
  injOn : ∀ a ∈ atoms F, ∀ b ∈ atoms F, v a = v b → a = b

instance [DecidableEq A] (v : A → Nat) (F : List (List (Signed A))) : Decidable (Coherent v F) :=
  decidable_of_iff ((∀ a ∈ atoms F, v a ≠ 0) ∧ ∀ a ∈ atoms F, ∀ b ∈ atoms F, v a = v b → a = b)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end Silmaril.Consequence.Gentzen.Clausal
