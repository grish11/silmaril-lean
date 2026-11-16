module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Regularity
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation

public section

/-!
# Original raw constructor separation and strict universe hierarchy

Original conversion embeds in the separately named confluent left-linear
extension. Its common reduct preserves both persistent outer constructors,
so those constructors must agree. No conversion-conservativity theorem is
needed. Only heads, not original conversion of components, are recovered.
An all-rule original typing induction then proves exact strict universe typing.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Parallel development preserves every persistent outer constructor. -/
theorem LinearJ.Parallel.rigidHead {n : ℕ} {t u : Term n} {k : RigidHead}
    (h : LinearJ.Parallel t u) (ht : Term.rigidHead t = some k) : Term.rigidHead u = some k :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.parallel_head h ht

/-- Extended finite computation preserves every persistent outer constructor. -/
theorem LinearJ.Reduces.rigidHead {n : ℕ} {t u : Term n} {k : RigidHead}
    (h : LinearJ.Reduces t u) (ht : Term.rigidHead t = some k) : Term.rigidHead u = some k :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.reduces_head h ht

/-- Original raw conversion equates persistent outer constructors only when their tags agree. -/
theorem Convertible.rigidHead_eq {n : ℕ} {t u : Term n} {k l : RigidHead}
    (h : Convertible t u) (ht : Term.rigidHead t = some k) (hu : Term.rigidHead u = some l) : k = l :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.convertible_head_eq h ht hu

/-- Incompatible persistent heads cannot be related by original raw conversion. -/
theorem not_convertible_of_rigidHead_ne {n : ℕ} {t u : Term n} {k l : RigidHead}
    (ht : Term.rigidHead t = some k) (hu : Term.rigidHead u = some l) (hkl : k ≠ l) : ¬ Convertible t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_of_head_ne ht hu hkl

/-- Original raw conversion cannot identify distinct indexed universes. -/
theorem convertible_univ_iff {n i j : ℕ} :
    Convertible (.univ i : Term n) (.univ j) ↔ i = j :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.convertible_univ_iff

/-- Original raw universes inhabit exactly the strictly higher universes in a well-formed telescope. -/
theorem typing_univ_iff {n i j : ℕ} {Γ : Context n} :
    Typing Γ (.univ i) (.univ j) ↔ WellFormed Γ ∧ i < j :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.typing_univ_iff

/-- An original raw universe is not convertible to a dependent product. -/
theorem not_convertible_univ_pi {n i : ℕ} (A : Term n) (B : Term (n + 1)) :
    ¬ Convertible (.univ i) (.pi A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_univ_pi A B

/-- An original raw universe is not convertible to a dependent sum. -/
theorem not_convertible_univ_sigma {n i : ℕ} (A : Term n) (B : Term (n + 1)) :
    ¬ Convertible (.univ i) (.sigma A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_univ_sigma A B

/-- An original raw universe is not convertible to an identity type. -/
theorem not_convertible_univ_id {n i : ℕ} (A a b : Term n) :
    ¬ Convertible (.univ i) (.id A a b) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_univ_id A a b

/-- Original raw products and sums have incompatible outer constructors. -/
theorem not_convertible_pi_sigma {n : ℕ} (A A' : Term n) (B B' : Term (n + 1)) :
    ¬ Convertible (.pi A B) (.sigma A' B') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_pi_sigma A A' B B'

/-- Original raw natural and empty types are not convertible. -/
theorem not_convertible_nat_empty {n : ℕ} :
    ¬ Convertible (.nat : Term n) .empty :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_nat_empty

/-- Original raw natural and unit types are not convertible. -/
theorem not_convertible_nat_unit {n : ℕ} :
    ¬ Convertible (.nat : Term n) .unit :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_nat_unit

/-- Original raw empty and unit types are not convertible. -/
theorem not_convertible_empty_unit {n : ℕ} :
    ¬ Convertible (.empty : Term n) .unit :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_convertible_empty_unit

/-- No original raw universe inhabits itself. -/
theorem not_typing_univ_self {n i : ℕ} (Γ : Context n) : ¬ Typing Γ (.univ i) (.univ i) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.not_typing_univ_self Γ

/-- Every original typing of a universe has a convertible strictly higher universe carrier. -/
theorem Derivation.univ_generation {n i : ℕ} {Γ : Context n} {A : Term n}
    (h : Derivation Γ (.univ i) A) : ∃ j, i < j ∧ Convertible A (.univ j) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawHeadSeparation.universe_generation h i rfl

end Silmaril.Logic.TypeTheory.IntensionalMLTT
