module

public import Silmaril.Logic.Consequence.Gentzen.Calculus.Defs
public import Silmaril.Logic.Consequence.Gentzen.Translate.Defs
public import Silmaril.Logic.Consequence.Shape.Defs

/-!
# Clausal acceptors: UNSAT, TAUTO, CNF and Gentzen, with their closure properties

Four kinds of acceptor over a formula type `C`, each a plain predicate (an *acceptor policy*,
with no semantics attached):

| kind | type | list read as |
|---|---|---|
| UNSAT acceptor `U` | `List C → Prop` | a conjunction, accepted when refuted |
| TAUTO acceptor `T` | `List C → Prop` | a disjunction, accepted when valid |
| CNF acceptor `A` | `List (List C) → Prop` | a conjunction of disjunctions (clauses), accepted when refuted |
| Gentzen acceptor `S` | `Seq C` (`List C → List C → Prop`) | a sequent `Γ ⊢ Δ` |

**Semantics is separate.** Over `sat : M → C → Prop`: `ClauseSat sat m K` (some member of `K`
holds), `CnfSat sat m F` (every clause of `F` does), `CnfUnsat sat F` (no model of the model
type `M` satisfies `F`; satisfiability is relative to `M`). An acceptor is `CnfSound`
(accepts only refuted formulas) or `CnfComplete` (accepts all of them); neither is a closure
property, and a sound checker need not be closed (`…Clausal.Examples`).

**Closure properties.** Weakening is ordinary membership inclusion `⊆` throughout (the
existing `ListPred.UpClosed`); order- or multiplicity-sensitive policies are opt-in elsewhere
(`Gentzen.withWeakening`) and are not covered by the equivalences here. Negation is an explicit
function `neg : C → C`; no involution is assumed, and none is derivable from these laws alone.

* `UnsatClosed neg U`: `⊆`-weakening, explosion (`c` and `neg c` both present), and unit cut
  `U (neg a :: Γ) → U (a :: Γ') → U (Γ ++ Γ')`.
* `TautClosed neg T`: `⊆`-weakening, excluded middle, and cut `T (a :: Δ) → T (neg a :: Δ') →
  T (Δ ++ Δ')`.
* `GentzenClosed neg S`: closed under the default Gentzen rules (`Gentzen.defaultRules`:
  reflexivity, `⊆`-weakening on both sides, cut) with both negation rules `NegL`, `NegR`.
* Two CNF layers, kept apart:
  - `CnfClosed A`, **representation closure**: clause-set weakening, clause strengthening,
    clause splitting and the empty clause. It mentions no negation: it says only that `A`
    reads a CNF formula as the conjunction of disjunctions, i.e. that `A` is determined by its
    unit restriction (`unitsOf A`) through hitting sets (`cnfOf`).
  - `CnfUnsatClosed neg A`, **logical closure**: `CnfClosed A` plus complementary units
    `A [[c], [neg c]]` and unit resolution `A ([neg a] :: F) → A ([a] :: G) → A (F ++ G)`.
    These are exactly what makes `unitsOf A` an `UnsatClosed` acceptor (`…Clausal.Thms`).

**Conversions.** `units Γ` is the CNF of unit clauses of `Γ`; `unitsOf A Γ := A (units Γ)`.
`Hits Γ F` says that `Γ` meets every clause of `F`, and `cnfOf U F` accepts `F` when every
list hitting `F` is accepted by `U`. Between UNSAT and Gentzen acceptors the conversions are the
existing `toUnsat`, `viaUnsat` (and `toTaut`, `viaTauto` for TAUTO).

**Signed formulas.** Over `Signed A` with its sign flip (`-·`), `signedUnsat S Γ` is the
refutation restriction of the signed lift of a sequent relation on the atoms `A`, i.e.
`S (posAtoms Γ) (negAtoms Γ)`. No positive part is recovered from an involution: atoms are the
existing `Signed.pos` embedding and `MultiSystem.posPart`.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Clausal

universe u v

variable {C : Type u}

/-! ## Semantics -/

section Semantics

variable {M : Type v}

/-- Some literal of the clause `K` holds in `m`. -/
def ClauseSat (sat : M → C → Prop) (m : M) (K : List C) : Prop := ∃ c ∈ K, sat m c

/-- Every clause of `F` holds in `m`: `F` read as a conjunction of disjunctions. -/
def CnfSat (sat : M → C → Prop) (m : M) (F : List (List C)) : Prop :=
  ∀ K ∈ F, ClauseSat sat m K

/-- No model in `M` satisfies `F`. -/
def CnfUnsat (sat : M → C → Prop) (F : List (List C)) : Prop := ∀ m, ¬ CnfSat sat m F

/-- The acceptor accepts only formulas unsatisfiable in `M`. -/
def CnfSound (sat : M → C → Prop) (A : List (List C) → Prop) : Prop :=
  ∀ F, A F → CnfUnsat sat F

/-- The acceptor accepts every formula unsatisfiable in `M`. -/
def CnfComplete (sat : M → C → Prop) (A : List (List C) → Prop) : Prop :=
  ∀ F, CnfUnsat sat F → A F

end Semantics

/-! ## Conversions -/

/-- The CNF of unit clauses `[c]` for `c ∈ Γ`. -/
def units (Γ : List C) : List (List C) := Γ.map ([·])

/-- The unit restriction of a CNF acceptor: an UNSAT acceptor. -/
def unitsOf (A : List (List C) → Prop) (Γ : List C) : Prop := A (units Γ)

/-- `Γ` meets every clause of `F`. -/
def Hits (Γ : List C) (F : List (List C)) : Prop := ∀ K ∈ F, ∃ c ∈ K, c ∈ Γ

/-- The CNF acceptor of an UNSAT acceptor: every list hitting `F` is accepted. -/
def cnfOf (U : List C → Prop) (F : List (List C)) : Prop := ∀ Γ, Hits Γ F → U Γ

/-! ## Closure properties -/

/-- An UNSAT acceptor closed under `⊆`-weakening, explosion and unit cut. -/
structure UnsatClosed (neg : C → C) (U : List C → Prop) : Prop where
  up : ListPred.UpClosed U
  explode : ∀ ⦃Γ c⦄, c ∈ Γ → neg c ∈ Γ → U Γ
  cut : ∀ ⦃a Γ Γ'⦄, U (neg a :: Γ) → U (a :: Γ') → U (Γ ++ Γ')

/-- A TAUTO acceptor closed under `⊆`-weakening, excluded middle and cut. -/
structure TautClosed (neg : C → C) (T : List C → Prop) : Prop where
  up : ListPred.UpClosed T
  excluded : ∀ ⦃Δ c⦄, c ∈ Δ → neg c ∈ Δ → T Δ
  cut : ∀ ⦃a Δ Δ'⦄, T (a :: Δ) → T (neg a :: Δ') → T (Δ ++ Δ')

/-- A Gentzen acceptor closed under the default rules with both negation rules. -/
def GentzenClosed (neg : C → C) (S : Seq C) : Prop :=
  Closed defaultRules S ∧ NegL neg S ∧ NegR neg S

/-- Representation closure of a CNF acceptor: it reads lists of clauses as conjunctions of
disjunctions. No negation and no logical law is involved. -/
structure CnfClosed (A : List (List C) → Prop) : Prop where
  /-- More clauses (as a set) keep acceptance. -/
  up : ListPred.UpClosed A
  /-- A smaller clause (as a set) is stronger. -/
  strengthen : ∀ ⦃K K' F⦄, K' ⊆ K → A (K :: F) → A (K' :: F)
  /-- A clause `a ∨ K` is refuted by refuting `a` and `K` separately. -/
  split : ∀ ⦃a K F⦄, A ([a] :: F) → A (K :: F) → A ((a :: K) :: F)
  /-- The empty clause is refuted. -/
  empty : ∀ F, A ([] :: F)

/-- Logical closure of a CNF acceptor: representation closure, complementary units and unit
resolution. -/
structure CnfUnsatClosed (neg : C → C) (A : List (List C) → Prop) : Prop
    extends CnfClosed A where
  /-- Complementary units are refuted. -/
  complement : ∀ c, A [[c], [neg c]]
  /-- Unit resolution on `a`. -/
  unitCut : ∀ ⦃a F G⦄, A ([neg a] :: F) → A ([a] :: G) → A (F ++ G)

/-! ## Signed formulas -/

/-- The refutation restriction of the signed lift of `S`: `S (posAtoms Γ) (negAtoms Γ)`. -/
def signedUnsat {A : Type u} (S : Seq A) (Γ : List (Signed A)) : Prop :=
  toUnsat (signedLift S) Γ

/-- The sequent relation on atoms of a signed UNSAT acceptor: `Γ ⊢ Δ` iff
`[pos g | g ∈ Γ] ++ [neg d | d ∈ Δ]` is accepted (the positive part, along `Signed.pos`, of
its raw refutation relation). -/
def atomSeq {A : Type u} (U : List (Signed A) → Prop) : Seq A :=
  MultiSystem.posPart (viaUnsat U (-·))

end Silmaril.Consequence.Gentzen.Clausal
