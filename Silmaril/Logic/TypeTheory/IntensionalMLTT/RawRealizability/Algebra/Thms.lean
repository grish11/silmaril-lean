module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Algebra.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra

public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem of_rep {n : ℕ} (q : Value n) : ofTerm (rep q) = q :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.of_rep q

theorem ofTerm_eq_iff {n : ℕ} {t u : Term n} :
    ofTerm t = ofTerm u ↔ LinearJ.Convertible t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.ofTerm_eq_iff

theorem conv_map {n m : ℕ} (F : Term n → Term m)
    (hF : ∀ {a b}, LinearJ.Parallel a b → LinearJ.Parallel (F a) (F b))
    {t u : Term n} (h : LinearJ.Convertible t u) : LinearJ.Convertible (F t) (F u) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.conv_map F hF h

theorem conv₂ {n m k : ℕ} (F : Term n → Term m → Term k)
    (hF : ∀ {a a' b b'}, LinearJ.Parallel a a' → LinearJ.Parallel b b' →
      LinearJ.Parallel (F a b) (F a' b'))
    {a a' : Term n} {b b' : Term m} (ha : LinearJ.Convertible a a')
    (hb : LinearJ.Convertible b b') : LinearJ.Convertible (F a b) (F a' b') :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.conv₂ F hF ha hb

theorem pi_conv {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (h : LinearJ.Convertible (.pi A B) (.pi A' B')) :
    LinearJ.Convertible A A' ∧ LinearJ.Convertible B B' :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.pi_conv h

theorem sigma_conv {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (h : LinearJ.Convertible (.sigma A B) (.sigma A' B')) :
    LinearJ.Convertible A A' ∧ LinearJ.Convertible B B' :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.sigma_conv h

theorem id_conv {n : ℕ} {A A' a a' b b' : Term n}
    (h : LinearJ.Convertible (.id A a b) (.id A' a' b')) :
    LinearJ.Convertible A A' ∧ LinearJ.Convertible a a' ∧ LinearJ.Convertible b b' :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.id_conv h

theorem pi_inj {n : ℕ} {A A' : Value n} {B B' : Value (n + 1)}
    (h : pi A B = pi A' B') : A = A' ∧ B = B' :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.pi_inj h

theorem sigma_inj {n : ℕ} {A A' : Value n} {B B' : Value (n + 1)}
    (h : sigma A B = sigma A' B') : A = A' ∧ B = B' :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.sigma_inj h

theorem id_inj {n : ℕ} {A A' a a' b b' : Value n}
    (h : id A a b = id A' a' b') : A = A' ∧ a = a' ∧ b = b' :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.id_inj h

theorem HasHead.unique {n : ℕ} {q q' : Value n} {k l : RigidHead}
    (hq : HasHead q k) (hq' : HasHead q' l) (heq : q = q') : k = l :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.HasHead.unique hq hq' heq

theorem head_eq {n : ℕ} {q : Value n} {k : RigidHead} (hq : HasHead q k) : head q = some k :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_eq hq

@[simp] theorem head_nat : head nat = some .nat :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_nat

@[simp] theorem head_empty : head empty = some .empty :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_empty

@[simp] theorem head_unit : head unit = some .unit :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_unit

@[simp] theorem head_univ (i : ℕ) : head (univ i) = some (.univ i) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_univ i

@[simp] theorem head_pi {n : ℕ} (A : Value n) (B : Value (n + 1)) :
    head (pi A B) = some .pi :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_pi A B

@[simp] theorem head_sigma {n : ℕ} (A : Value n) (B : Value (n + 1)) :
    head (sigma A B) = some .sigma :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_sigma A B

@[simp] theorem head_id {n : ℕ} (A a b : Value n) :
    head (id A a b) = some .id :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.head_id A a b

theorem univ_inj {i j : ℕ} (h : univ i = univ j) : i = j :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra.univ_inj h

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
