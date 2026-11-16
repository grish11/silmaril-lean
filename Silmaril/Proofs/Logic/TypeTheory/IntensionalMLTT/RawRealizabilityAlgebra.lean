module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Algebra.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem of_rep {n : ℕ} (q : Value n) : ofTerm (rep q) = q := Quotient.out_eq q

theorem ofTerm_eq_iff {n : ℕ} {t u : Term n} :
    ofTerm t = ofTerm u ↔ LinearJ.Convertible t u :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem conv_map {n m : ℕ} (F : Term n → Term m)
    (hF : ∀ {a b}, LinearJ.Parallel a b → LinearJ.Parallel (F a) (F b))
    {t u : Term n} (h : LinearJ.Convertible t u) : LinearJ.Convertible (F t) (F u) := by
  induction h with
  | rel a b hab => exact .rel _ _ (hF hab)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h k ih ik => exact .trans _ _ _ ih ik

theorem conv₂ {n m k : ℕ} (F : Term n → Term m → Term k)
    (hF : ∀ {a a' b b'}, LinearJ.Parallel a a' → LinearJ.Parallel b b' →
      LinearJ.Parallel (F a b) (F a' b'))
    {a a' : Term n} {b b' : Term m} (ha : LinearJ.Convertible a a')
    (hb : LinearJ.Convertible b b') : LinearJ.Convertible (F a b) (F a' b') :=
  .trans _ _ _ (conv_map (fun x => F x b) (fun h => hF h (LinearJ.Parallel.rfl b)) ha)
    (conv_map (F a') (fun h => hF (LinearJ.Parallel.rfl a') h) hb)

theorem pi_reduces {n : ℕ} {A : Term n} {B : Term (n + 1)} {v : Term n}
    (h : LinearJ.Reduces (.pi A B) v) :
    ∃ A' B', v = .pi A' B' ∧ LinearJ.Reduces A A' ∧ LinearJ.Reduces B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | @tail v w h hstep ih =>
    obtain ⟨A', B', hv, hA, hB⟩ := ih
    cases hv
    cases hstep with
    | pi hA' hB' => exact ⟨_, _, rfl, hA.tail hA', hB.tail hB'⟩

theorem sigma_reduces {n : ℕ} {A : Term n} {B : Term (n + 1)} {v : Term n}
    (h : LinearJ.Reduces (.sigma A B) v) :
    ∃ A' B', v = .sigma A' B' ∧ LinearJ.Reduces A A' ∧ LinearJ.Reduces B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | @tail v w h hstep ih =>
    obtain ⟨A', B', hv, hA, hB⟩ := ih
    cases hv
    cases hstep with
    | sigma hA' hB' => exact ⟨_, _, rfl, hA.tail hA', hB.tail hB'⟩

theorem id_reduces {n : ℕ} {A a b v : Term n}
    (h : LinearJ.Reduces (.id A a b) v) :
    ∃ A' a' b', v = .id A' a' b' ∧ LinearJ.Reduces A A' ∧
      LinearJ.Reduces a a' ∧ LinearJ.Reduces b b' := by
  induction h with
  | refl => exact ⟨A, a, b, rfl, .refl, .refl, .refl⟩
  | @tail v w h hstep ih =>
    obtain ⟨A', a', b', hv, hA, ha, hb⟩ := ih
    cases hv
    cases hstep with
    | id hA' ha' hb' => exact ⟨_, _, _, rfl, hA.tail hA', ha.tail ha', hb.tail hb'⟩

theorem pi_conv {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (h : LinearJ.Convertible (.pi A B) (.pi A' B')) :
    LinearJ.Convertible A A' ∧ LinearJ.Convertible B B' := by
  obtain ⟨v, hL, hR⟩ := LinearJ.convertible_iff_join.mp h
  obtain ⟨C, D, hv, hA, hB⟩ := pi_reduces hL
  obtain ⟨C', D', hv', hA', hB'⟩ := pi_reduces hR
  have heq : Term.pi C D = .pi C' D' := hv.symm.trans hv'
  cases heq
  exact ⟨LinearJ.convertible_iff_join.mpr ⟨_, hA, hA'⟩,
    LinearJ.convertible_iff_join.mpr ⟨_, hB, hB'⟩⟩

theorem sigma_conv {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (h : LinearJ.Convertible (.sigma A B) (.sigma A' B')) :
    LinearJ.Convertible A A' ∧ LinearJ.Convertible B B' := by
  obtain ⟨v, hL, hR⟩ := LinearJ.convertible_iff_join.mp h
  obtain ⟨C, D, hv, hA, hB⟩ := sigma_reduces hL
  obtain ⟨C', D', hv', hA', hB'⟩ := sigma_reduces hR
  have heq : Term.sigma C D = .sigma C' D' := hv.symm.trans hv'
  cases heq
  exact ⟨LinearJ.convertible_iff_join.mpr ⟨_, hA, hA'⟩,
    LinearJ.convertible_iff_join.mpr ⟨_, hB, hB'⟩⟩

theorem id_conv {n : ℕ} {A A' a a' b b' : Term n}
    (h : LinearJ.Convertible (.id A a b) (.id A' a' b')) :
    LinearJ.Convertible A A' ∧ LinearJ.Convertible a a' ∧ LinearJ.Convertible b b' := by
  obtain ⟨v, hL, hR⟩ := LinearJ.convertible_iff_join.mp h
  obtain ⟨C, x, y, hv, hA, ha, hb⟩ := id_reduces hL
  obtain ⟨C', x', y', hv', hA', ha', hb'⟩ := id_reduces hR
  have heq : Term.id C x y = .id C' x' y' := hv.symm.trans hv'
  cases heq
  exact ⟨LinearJ.convertible_iff_join.mpr ⟨_, hA, hA'⟩,
    LinearJ.convertible_iff_join.mpr ⟨_, ha, ha'⟩,
    LinearJ.convertible_iff_join.mpr ⟨_, hb, hb'⟩⟩

theorem pi_inj {n : ℕ} {A A' : Value n} {B B' : Value (n + 1)}
    (h : pi A B = pi A' B') : A = A' ∧ B = B' := by
  obtain ⟨hA, hB⟩ := pi_conv (ofTerm_eq_iff.mp h)
  exact ⟨(of_rep A).symm.trans ((ofTerm_eq_iff.mpr hA).trans (of_rep A')),
    (of_rep B).symm.trans ((ofTerm_eq_iff.mpr hB).trans (of_rep B'))⟩

theorem sigma_inj {n : ℕ} {A A' : Value n} {B B' : Value (n + 1)}
    (h : sigma A B = sigma A' B') : A = A' ∧ B = B' := by
  obtain ⟨hA, hB⟩ := sigma_conv (ofTerm_eq_iff.mp h)
  exact ⟨(of_rep A).symm.trans ((ofTerm_eq_iff.mpr hA).trans (of_rep A')),
    (of_rep B).symm.trans ((ofTerm_eq_iff.mpr hB).trans (of_rep B'))⟩

theorem id_inj {n : ℕ} {A A' a a' b b' : Value n}
    (h : id A a b = id A' a' b') : A = A' ∧ a = a' ∧ b = b' := by
  obtain ⟨hA, ha, hb⟩ := id_conv (ofTerm_eq_iff.mp h)
  exact ⟨(of_rep A).symm.trans ((ofTerm_eq_iff.mpr hA).trans (of_rep A')),
    (of_rep a).symm.trans ((ofTerm_eq_iff.mpr ha).trans (of_rep a')),
    (of_rep b).symm.trans ((ofTerm_eq_iff.mpr hb).trans (of_rep b'))⟩
theorem HasHead.unique {n : ℕ} {q q' : Value n} {k l : RigidHead}
    (hq : HasHead q k) (hq' : HasHead q' l) (heq : q = q') : k = l := by
  obtain ⟨t, ht, hk⟩ := hq
  obtain ⟨u, hu, hl⟩ := hq'
  have hconv : LinearJ.Convertible t u := ofTerm_eq_iff.mp (ht.trans (heq.trans hu.symm))
  obtain ⟨v, htv, huv⟩ := LinearJ.convertible_iff_join.mp hconv
  have hkv : v.rigidHead = some k := htv.rigidHead hk
  have hlv : v.rigidHead = some l := huv.rigidHead hl
  exact Option.some.inj (hkv.symm.trans hlv)

theorem head_eq {n : ℕ} {q : Value n} {k : RigidHead} (hq : HasHead q k) : head q = some k := by
  have hex : ∃ l, HasHead q l := ⟨k, hq⟩
  have hchosen : HasHead q (Classical.choose hex) := Classical.choose_spec hex
  have heq : Classical.choose hex = k := HasHead.unique hchosen hq rfl
  simp only [head, dite_eq_left hex, heq]

@[simp] theorem head_nat : head nat = some .nat := head_eq ⟨.nat, rfl, rfl⟩
@[simp] theorem head_empty : head empty = some .empty := head_eq ⟨.empty, rfl, rfl⟩
@[simp] theorem head_unit : head unit = some .unit := head_eq ⟨.unit, rfl, rfl⟩
@[simp] theorem head_univ (i : ℕ) : head (univ i) = some (.univ i) := head_eq ⟨.univ i, rfl, rfl⟩
@[simp] theorem head_pi {n : ℕ} (A : Value n) (B : Value (n + 1)) :
    head (pi A B) = some .pi := head_eq ⟨_, rfl, rfl⟩
@[simp] theorem head_sigma {n : ℕ} (A : Value n) (B : Value (n + 1)) :
    head (sigma A B) = some .sigma := head_eq ⟨_, rfl, rfl⟩
@[simp] theorem head_id {n : ℕ} (A a b : Value n) :
    head (id A a b) = some .id := head_eq ⟨_, rfl, rfl⟩

theorem univ_inj {i j : ℕ} (h : univ i = univ j) : i = j :=
  RigidHead.univ.inj (Option.some.inj (by simpa only [head_univ] using congrArg head h))


end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityAlgebra
