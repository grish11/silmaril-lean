module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Rounds.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonRounds

/-! # Unrolling laws: from two and three rounds to written loops

The statements hold in any contextual extension of Paper. The two- and
three-round laws are premises here.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds

open Silmaril.Isotope.LambdaSSA (VCtx LCtx)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {A B : τ}

/-- A larger seed keeps every equation between projected arrows. -/
theorem projection_map_of_le {Small : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (incl : ∀ {Γ r s L}, Small Γ r s L → Seed Γ r s L)
    {X Y : Paper.TypeCategory (τ := τ) Φ} {a b : X ⟶ Y}
    (h : (projection Small).map a = (projection Small).map b) :
    (projection Seed).map a = (projection Seed).map b :=
  SingletonRounds.projection_map_of_le Seed incl h

theorem roundsRegion_typed {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) :
    ValueBranches [A] (roundsRegion s n) [Silmaril.coprod B A] :=
  SingletonRounds.rounds_typed hs n

/-- The written rounds represent the categorical rounds of the same step. -/
theorem ofRegion_roundsRegion {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A])
    (n : Nat) : ofRegion Seed (roundsRegion_typed hs n) = rounds Seed (ofRegion Seed hs) n :=
  SingletonRounds.ofRegion_rounds Seed hs n

/-- Rounds add: `m + 1` rounds followed on repeat by `n + 1` rounds. -/
theorem rounds_add (s : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A)) (m n : Nat) :
    thenExact Seed (rounds Seed s m) (rounds Seed s n) = rounds Seed s (m + n + 1) :=
  SingletonRounds.rounds_add Seed s m n

/-- Rounds of rounds: `n + 1` blocks of `m + 1` rounds are `(m + 1) * (n + 1)` rounds. -/
theorem rounds_rounds (s : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A)) (m n : Nat) :
    rounds Seed (rounds Seed s m) n = rounds Seed s (m * n + m + n) :=
  SingletonRounds.rounds_rounds Seed s m n

/-- The laws for round counts `m + 1` and `n + 1` give the law for their
product. So a quotient unrolls every round count exactly when it unrolls
every prime one, and each missing prime is a separate law. -/
theorem Unrolls.mul {m n : Nat} (hm : Unrolls Seed m) (hn : Unrolls Seed n) :
    Unrolls Seed (m * n + m + n) :=
  SingletonRounds.unrolls_mul Seed hm hn

/-- With the two- and three-round laws, every round count that is a
product of twos and threes unrolls, at every step of the quotient. -/
theorem unrolls_of_smooth (double : Doubles Seed) (triple : Triples Seed) {n : Nat} (h : Smooth n) :
    Unrolls Seed n :=
  SingletonRounds.unrolls_of_smooth Seed double triple h

/-- The law at the chosen coproduct gives the law at the exact sum. -/
theorem unrolls_of_roundsLaw {n : Nat} (law : RoundsLaw Seed n) : Unrolls Seed n :=
  SingletonRounds.unrolls_of_roundsLaw Seed law

/-- An unrolling law equates the written loop on `n + 1` rounds of a
guarded step with the written loop on one round. -/
theorem unrolled_eqv {n : Nat} (law : Unrolls Seed n) {s : Region Φ}
    (hs : ValueBranches [A] s [Silmaril.coprod B A]) :
    Paper.Extension.Eqv Seed [A] (SyntacticCategory.iterateRegion A (roundsRegion s n))
      (SyntacticCategory.iterateRegion A s) [B] :=
  SingletonRounds.unrolled_eqv Seed law hs

/-- The law for `n + 1` rounds is exactly the family of written loop
equations at all guarded steps. -/
theorem unrolls_iff (n : Nat) :
    Unrolls Seed n ↔
      ∀ {A B : τ} {s : Region Φ} (_ : ValueBranches [A] s [Silmaril.coprod B A]),
        Paper.Extension.Eqv Seed [A] (SyntacticCategory.iterateRegion A (roundsRegion s n))
          (SyntacticCategory.iterateRegion A s) [B] :=
  ⟨fun law _ _ _ hs => unrolled_eqv Seed law hs, SingletonRounds.unrolls_of_eqv Seed⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds
