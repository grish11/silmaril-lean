module

public import Silmaril.Containers.Runtime.Defs

/-!
# Preconditions on image contents, relative to a runtime model

Given a runtime model `R` and a specification `φ` (from an interface: a profile, ports, an HTTP
or exit-status contract), which images satisfy `φ` when started under `R`? The baseline answer
is semantic and always exists:

* `pre R φ i`: every run of the image `i` under `R` satisfies `φ`. It is the **weakest**
  precondition in the semantic sense: it is sufficient, and every sufficient predicate implies
  it (`Thms.pre_weakest`). For flat images `i` is the contents (`Flat C`), so `pre R φ` is a
  predicate on contents; for layered images it reduces to the flat case plus refusals
  (`Thms.pre_layered`);
* `vpre R φ := pre R (noUB ∧ φ)`, the **verification precondition**: no run has undefined
  behaviour (`Spec.noUB`), universally over the runs of `R`, and every run satisfies `φ`.
  Undefined behaviour is an explicit outcome of runs (`Stop.undefined`), never an absence of
  runs, so it cannot make a precondition hold vacuously (`Thms.not_vpre_of_undefined`);
* `wlp R post := vpre R (partialCorrect post)`, the weakest *liberal* precondition: crashes,
  divergence, blocking, kills and refusals are allowed; undefined behaviour is not;
* `wp R post := vpre R (totalCorrect post)`: every run exits and satisfies `post`.

"No undefined behaviour" is not termination or progress: `wlp` holds of a spinning program.

Both quantify over every run **under `R`**: they change when the runtime model changes, and a
weaker runtime model (more runs) gives a stronger precondition (`Thms.pre_antitone`).
A model with no runs for an image satisfies everything (`Thms.pre_of_infeasible`): feasibility
(`Feasible`) is a separate obligation, not implied by `pre`.

**Representability.** `pre R φ` is a predicate on contents in Lean's logic; whether it can be
written in a *given* assertion language (`Assertions`: formulas with a denotation on images),
for example a decidable checker over an image's files or a first-order theory of ELF facts, is
a separate question (`Representable`). This module does not assume that weakest preconditions
are expressible: an expressiveness result for a language is a hypothesis (`Expressive`), and
the practical object is a **concrete sufficient precondition** in the language
(`SufficientIn`): a formula together with a proof that it implies `pre R φ`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers

variable {I P E : Type}

/-- **The semantic precondition**: every run of the image under `R` satisfies `φ`. -/
def pre (R : Runtime I P E) (φ : Spec E) : I → Prop := fun i => (R.beh i).Sat φ

/-- **The verification precondition**: every run under `R` has no undefined behaviour and
satisfies `φ`. Every precondition used for verification is of this form. -/
def vpre (R : Runtime I P E) (φ : Spec E) : I → Prop := pre R fun b => Spec.noUB b ∧ φ b

/-- **The weakest liberal precondition** of a postcondition on exiting runs: no run has
undefined behaviour, and every run that exits satisfies `post`. Crashes, kills, refusals,
blocking and divergence are allowed. -/
def wlp (R : Runtime I P E) (post : List E → UInt8 → Prop) : I → Prop :=
  vpre R (Spec.partialCorrect post)

/-- **The weakest (total) precondition** of a postcondition on exiting runs: no run has
undefined behaviour, every run exits, and `post` holds. -/
def wp (R : Runtime I P E) (post : List E → UInt8 → Prop) : I → Prop :=
  vpre R (Spec.totalCorrect post)

/-- `Q` is a **sufficient precondition** for `φ` under `R`. -/
def Sufficient (R : Runtime I P E) (Q : I → Prop) (φ : Spec E) : Prop := ∀ i, Q i → pre R φ i

/-- The image has at least one run under `R`. -/
def Feasible (R : Runtime I P E) (i : I) : Prop := ∃ b, R.beh i b

/-- **An assertion language** over images: formulas and what they mean. -/
structure Assertions (I : Type) where
  F : Type
  den : F → I → Prop

/-- The predicate `Q` is written by some formula of `L`. -/
def Representable (L : Assertions I) (Q : I → Prop) : Prop := ∃ f, ∀ i, L.den f i ↔ Q i

/-- **Expressiveness** of `L` for `R` on the specifications `Φ`: every semantic precondition is
written by a formula. An assumption to be proved for each language, never a default. -/
def Expressive (L : Assertions I) (R : Runtime I P E) (Φ : Spec E → Prop) : Prop :=
  ∀ φ, Φ φ → Representable L (pre R φ)

/-- **A concrete sufficient precondition** in `L`: a formula and a proof that it implies the
semantic precondition. -/
structure SufficientIn (L : Assertions I) (R : Runtime I P E) (φ : Spec E) where
  pre : L.F
  sound : ∀ i, L.den pre i → Silmaril.Containers.pre R φ i

/-- Decidable predicates on images, as an assertion language (checkers). -/
def Assertions.bool (I : Type) : Assertions I := ⟨I → Bool, fun f i => f i = true⟩

end Silmaril.Containers
