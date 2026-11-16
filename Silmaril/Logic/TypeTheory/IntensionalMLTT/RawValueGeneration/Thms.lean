module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Thms
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration

public section

/-!
# Original constructor generation modulo carrier conversion

Every original typing tree of a value constructor recovers its actual
introduction-rule premises and a conversion from the requested carrier to
the native carrier. The all-rule induction includes conversion and
cumulativity; persistent-head separation rules out a universe carrier for
these value constructors. No new typing calculus, conversion-component
injectivity or normalization theorem is assumed.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Lambdas recover their actual annotation, body typing and dependent product carrier. -/
theorem Derivation.lam_generation {n : ℕ} {Γ : Context n} {A T : Term n} {body : Term (n + 1)}
    (h : Derivation Γ (.lam A body) T) :
    ∃ i j B, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) ∧
      Typing (Γ.snoc A) body B ∧ Convertible T (.pi A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.lam_generation h

/-- Pairs recover actual dependent sum formation and component typings. -/
theorem Derivation.pair_generation {n : ℕ} {Γ : Context n} {a b T : Term n}
    (h : Derivation Γ (.pair a b) T) :
    ∃ i j A B, Typing Γ A (.univ i) ∧ Typing (Γ.snoc A) B (.univ j) ∧
      Typing Γ a A ∧ Typing Γ b (B.instantiate a) ∧ Convertible T (.sigma A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.pair_generation h

/-- Zero has a carrier convertible to the original natural type. -/
theorem Derivation.zero_generation {n : ℕ} {Γ : Context n} {T : Term n}
    (h : Derivation Γ .zero T) : Convertible T .nat :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.zero_generation h

/-- Successor recovers an actual natural predecessor typing and natural carrier. -/
theorem Derivation.succ_generation {n : ℕ} {Γ : Context n} {a T : Term n}
    (h : Derivation Γ (.succ a) T) : Typing Γ a .nat ∧ Convertible T .nat :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.succ_generation h

/-- The unit witness has a carrier convertible to the original unit type. -/
theorem Derivation.star_generation {n : ℕ} {Γ : Context n} {T : Term n}
    (h : Derivation Γ .star T) : Convertible T .unit :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.star_generation h

/-- Reflexivity recovers actual endpoint formation and its based identity carrier. -/
theorem Derivation.refl_generation {n : ℕ} {Γ : Context n} {a T : Term n}
    (h : Derivation Γ (.refl a) T) :
    ∃ i A, Typing Γ A (.univ i) ∧ Typing Γ a A ∧ Convertible T (.id A a a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawValueGeneration.refl_generation h

end Silmaril.Logic.TypeTheory.IntensionalMLTT
