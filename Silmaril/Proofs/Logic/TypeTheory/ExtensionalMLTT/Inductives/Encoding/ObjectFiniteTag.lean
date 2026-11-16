module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag
open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Logic.SetTheory

universe u

private theorem lastCases_one {k : ℕ} (a : Tm (k + 2)) :
    Fin.lastCases (motive := fun _ => Tm (k + 2)) a Tm.bv
      (1 : Fin (k + 3)) = Tm.bv 1 := by
  change Fin.lastCases (motive := fun _ => Tm (k + 2)) a Tm.bv
    (Fin.castSucc (1 : Fin (k + 2))) = Tm.bv 1
  exact Fin.lastCases_castSucc _

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one_last {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

theorem cutoff_open (count : ℕ) {k : ℕ} (t : Tm (k + 1)) (x : String) :
    (cutoff count t).open x = cutoff count (t.open x) := by
  induction count generalizing k with
  | zero => simp only [cutoff, Tm.open]
  | succ count ih => simp only [cutoff, Tm.open, ih, lastCases_one]

theorem cutoff_lst (count : ℕ) {k : ℕ} (t : Tm (k + 1)) (a : Tm 0) :
    (cutoff count t).lst a = cutoff count (t.lst a) := by
  induction count generalizing k with
  | zero => simp only [cutoff, Tm.lst]
  | succ count ih => simp only [cutoff, Tm.lst, ih, lastCases_one]

theorem cutoff_wkn (count : ℕ) {k : ℕ} (t : Tm k) (j : ℕ) :
    (cutoff count t).wkn j = cutoff count (t.wkn j) := by
  induction count generalizing k j with
  | zero => simp only [cutoff, Tm.wkn]
  | succ count ih =>
      simp only [cutoff, Tm.wkn, ih]
      rw [ite_eq_left (by change 1 < j + 1 + 1; omega)]
      rfl

theorem cutoff_typing (count : ℕ) {Γ : Ctx} {t : Tm 0}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) (ht : Γ.JEqB 1 ∅ .nats t t) :
    Γ.JEqB 1 ∅ .nats (cutoff count t) (cutoff count t) := by
  induction count generalizing Γ t with
  | zero => exact .succ (.zero hΓ)
  | succ count ih =>
      show Γ.JEqB 1 ∅ .nats (cutoff (count + 1) t) (cutoff (count + 1) t)
      have hC : ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅ (.univ 0)
          ((.nats : Tm 1).open x) ((.nats : Tm 1).open x) := by
        intro x hx
        simpa only [Tm.open] using Ctx.JEqB.nats (n := 0) (by decide)
          (.cons_ok (n := 0) (by decide) hΓ hx (.nats (by decide) hΓ))
      have hs : ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅ (.arr .nats .nats)
          ((.abs .nats (cutoff count (.bv 1)) : Tm 1).open x)
          ((.abs .nats (cutoff count (.bv 1)) : Tm 1).open x) := by
        intro x hx
        have hX : (Γ.cons x .nats).JEqB 1 ∅ .unit .star .star :=
          .cons_ok (n := 0) (by decide) hΓ hx (.nats (by decide) hΓ)
        simpa only [Tm.open, cutoff_open, lastCases_one_last, Tm.wk0,
          cutoff_wkn, Tm.wkn] using
          Ctx.JEqB.constant_abstraction (n := 0) (by decide) hX
            (.nats (by decide) hX) (.nats (by decide) hX)
            (ih hX (.var hX (.here Γ x .nats)))
      have hz : Γ.JEqB 1 ∅ ((.nats : Tm 1).lst .zero) .zero .zero := by
        simpa only [Tm.lst] using Ctx.JEqB.zero hΓ
      have hs' : ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅
          (.arr ((.nats : Tm 1).open x) ((.nats : Tm 1).lst (.succ (.fv x))))
          ((.abs .nats (cutoff count (.bv 1)) : Tm 1).open x)
          ((.abs .nats (cutoff count (.bv 1)) : Tm 1).open x) := by
        simpa only [Tm.open, Tm.lst] using hs
      simpa only [cutoff, Tm.lst, Tm.open] using
        Ctx.JEqB.natrec (n := 0) (L := Γ.dv) (by decide) hC hz hs' ht

private theorem numeral_typing (n : ℕ) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ .nats (Encoding.Object.UnitVector.numeral n)
      (Encoding.Object.UnitVector.numeral n) := by
  induction n with
  | zero => exact .zero hΓ
  | succ n ih => exact .succ ih

private theorem cutoff_motive {Γ : Ctx} (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅ (.univ 0)
      ((.nats : Tm 1).open x) ((.nats : Tm 1).open x) := by
  intro x hx
  simpa only [Tm.open] using Ctx.JEqB.nats (n := 0) (by decide)
    (.cons_ok (n := 0) (by decide) hΓ hx (.nats (by decide) hΓ))

private theorem cutoff_step (count : ℕ) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅
      (.arr ((.nats : Tm 1).open x) ((.nats : Tm 1).lst (.succ (.fv x))))
      ((.abs .nats (cutoff count (.bv 1)) : Tm 1).open x)
      ((.abs .nats (cutoff count (.bv 1)) : Tm 1).open x) := by
  intro x hx
  have hX : (Γ.cons x .nats).JEqB 1 ∅ .unit .star .star :=
    .cons_ok (n := 0) (by decide) hΓ hx (.nats (by decide) hΓ)
  simpa only [Tm.open, Tm.lst, cutoff_open, lastCases_one_last, Tm.wk0,
    cutoff_wkn, Tm.wkn] using
    Ctx.JEqB.constant_abstraction (n := 0) (by decide) hX
      (.nats (by decide) hX) (.nats (by decide) hX)
      (cutoff_typing count hX (.var hX (.here Γ x .nats)))

/-- The object equality rules compute the cutoff of every object numeral. -/
theorem cutoff_compute (count n : ℕ) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ .nats (cutoff count (Encoding.Object.UnitVector.numeral n))
      (Encoding.Object.UnitVector.numeral (code count n)) := by
  induction count generalizing n with
  | zero => exact numeral_typing 1 hΓ
  | succ count ih =>
      show Γ.JEqB 1 ∅ .nats (cutoff (count + 1) (Encoding.Object.UnitVector.numeral n))
        (Encoding.Object.UnitVector.numeral (code (count + 1) n))
      have hz : Γ.JEqB 1 ∅ ((.nats : Tm 1).lst .zero) .zero .zero := by
        simpa only [Tm.lst] using Ctx.JEqB.zero hΓ
      cases n with
      | zero =>
          simpa only [cutoff, Encoding.Object.FiniteTag.code, Encoding.Object.UnitVector.numeral, Tm.lst] using
            Ctx.JEqB.beta_natrec_zero (n := 0) (by decide)
              (cutoff_motive hΓ) hz (cutoff_step count hΓ)
      | succ n =>
          show Γ.JEqB 1 ∅ .nats
            (cutoff (count + 1) (Encoding.Object.UnitVector.numeral (n + 1)))
            (Encoding.Object.UnitVector.numeral (code (count + 1) (n + 1)))
          have hembed := Tm.wkn_past (Encoding.Object.UnitVector.numeral n : Tm 0)
            0 (Nat.le_refl 0)
          have hβ : Γ.JEqB 1 ∅ .nats
              (cutoff (count + 1) (Encoding.Object.UnitVector.numeral (n + 1)))
              (.app (.abs .nats ((cutoff count
                (Encoding.Object.UnitVector.numeral n) : Tm 0).wk0))
                (cutoff (count + 1) (Encoding.Object.UnitVector.numeral n))) := by
            simpa only [cutoff, Encoding.Object.UnitVector.numeral, Tm.lst, cutoff_lst,
              lastCases_one_last, Tm.wk0, cutoff_wkn, hembed] using
              Ctx.JEqB.beta_natrec_succ (n := 0) (by decide)
                (cutoff_motive hΓ) hz (cutoff_step count hΓ) (numeral_typing n hΓ)
          have hb := cutoff_typing count hΓ (numeral_typing n hΓ)
          have hB := Ctx.JEqB.constant_family (n := 0) (by decide) hΓ
            (Ctx.JEqB.nats (n := 0) (by decide) hΓ) (Ctx.JEqB.nats (n := 0) (by decide) hΓ)
          have hbody : ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅
              ((.nats : Tm 0).wk0.open x)
              ((cutoff count (Encoding.Object.UnitVector.numeral n) : Tm 0).wk0.open x)
              ((cutoff count (Encoding.Object.UnitVector.numeral n) : Tm 0).wk0.open x) := by
            intro x hx
            simpa only [Tm.closed_wk0_open] using
              hΓ.weaken_cons hx (n := 0) (by decide) (.nats (by decide) hΓ) hb
          have hβ' := Ctx.JEqB.beta_app (n := 0) (by decide)
            (Ctx.JEqB.nats (n := 0) (by decide) hΓ) hB hbody
            (cutoff_typing (count + 1) hΓ (numeral_typing n hΓ))
          have hβ'' : Γ.JEqB 1 ∅ .nats
              (.app (.abs .nats ((cutoff count
                (Encoding.Object.UnitVector.numeral n) : Tm 0).wk0))
                (cutoff (count + 1) (Encoding.Object.UnitVector.numeral n)))
              (cutoff count (Encoding.Object.UnitVector.numeral n)) := by
            simpa only [Tm.closed_wk0_lst] using hβ'
          exact hβ.trans (hβ''.trans (ih n))

theorem formation (count : ℕ) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ (.univ 0) (Tag count) (Tag count) := by
  apply Ctx.JEqB.sigma (n := 0) (L := Γ.dv) (by decide) (.nats (by decide) hΓ)
  intro x hx
  have hX : (Γ.cons x .nats).JEqB 1 ∅ .unit .star .star :=
    .cons_ok (n := 0) (by decide) hΓ hx (.nats (by decide) hΓ)
  simpa only [Tm.open, cutoff_open, lastCases_zero] using
    Ctx.JEqB.id (n := 0) (by decide) (.nats (by decide) hX)
      (cutoff_typing count hX (.var hX (.here Γ x .nats))) (.zero hX)

theorem code_eq_zero_iff (count n : ℕ) : code count n = 0 ↔ n < count := by
  induction count generalizing n with
  | zero => simp [Encoding.Object.FiniteTag.code]
  | succ count ih => cases n <;> simp [Encoding.Object.FiniteTag.code, ih]

/-- Every host finite tag has an actual one-universe object derivation. -/
theorem canonical_typing {count : ℕ} (i : Fin count) {Γ : Ctx}
    (hΓ : Γ.JEqB 1 ∅ .unit .star .star) :
    Γ.JEqB 1 ∅ (Tag count) (canonical i) (canonical i) := by
  have hB : ∀ x ∉ Γ.dv, (Γ.cons x .nats).JEqB 1 ∅ (.univ 0)
      ((.id .nats (cutoff count (.bv 0)) .zero : Tm 1).open x)
      ((.id .nats (cutoff count (.bv 0)) .zero : Tm 1).open x) := by
    intro x hx
    have hX : (Γ.cons x .nats).JEqB 1 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) hΓ hx (.nats (by decide) hΓ)
    simpa only [Tm.open, cutoff_open, lastCases_zero] using
      Ctx.JEqB.id (n := 0) (by decide) (.nats (by decide) hX)
        (cutoff_typing count hX (.var hX (.here Γ x .nats))) (.zero hX)
  apply Ctx.JEqB.pair (n := 0) (L := Γ.dv) (by decide)
    (.nats (by decide) hΓ) hB (numeral_typing i.val hΓ)
  have hc : Γ.JEqB 1 ∅ .nats (cutoff count (Encoding.Object.UnitVector.numeral i.val)) .zero := by
    simpa only [(code_eq_zero_iff count i.val).2 i.isLt, Encoding.Object.UnitVector.numeral] using
      cutoff_compute count i.val hΓ
  have hId := Ctx.JEqB.id (n := 0) (by decide) (.nats (by decide) hΓ)
    hc.symm (Ctx.JEqB.zero hΓ)
  simpa only [Tm.lst, cutoff_lst, lastCases_zero, Tm.castLE_refl] using
    Ctx.JEqB.conv (n := 0) (by decide) hId (.refl (.zero hΓ))

theorem cutoff_denoteIn (count n : ℕ) {k : ℕ} (t : Tm k)
    (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u})
    (ht : t.denoteIn U ρ β = numeral n) :
    (cutoff count t).denoteIn U ρ β = numeral (code count n) := by
  induction count generalizing k n with
  | zero => rfl
  | succ count ih =>
      simp only [cutoff, Tm.denoteIn, ht, SetSem.natrec_numeral]
      clear ht t
      induction n with
      | zero => rfl
      | succ n hn =>
          change SetSem.app (SetSem.lam ZFSet.omega
            (fun acc => (cutoff count (.bv 1 : Tm (k + 2))).denoteIn U ρ
              (Fin.cons acc (Fin.cons (numeral n) β)))) _ = _
          rw [SetSem.app_lam _ (hn.symm ▸ numeral_mem_omega (code (count + 1) n))]
          exact ih n (.bv 1) _ rfl

/-- Every semantic tag is exactly one of the finitely many canonical pairs. -/
theorem mem_denoteIn_iff (count : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (p : ZFSet.{u}) :
    p ∈ (Tag count : Tm 0).denoteIn U ρ Fin.elim0 ↔
      ∃ i : Fin count, p = SetSem.pair (numeral i.val) ∅ := by
  simp only [Tag, Tm.denoteIn, SetSem.mem_sigma, SetSem.mem_truth]
  constructor
  · rintro ⟨a, ha, b, ⟨he, rfl⟩, hp⟩
    obtain ⟨n, rfl⟩ := mem_omega_iff.1 ha
    have hc := cutoff_denoteIn count n (.bv 0 : Tm 1) U ρ (Fin.cons (numeral n) Fin.elim0) rfl
    have hn : n < count := (code_eq_zero_iff count n).1 (numeral_injective (hc.symm.trans he))
    exact ⟨⟨n, hn⟩, hp.symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨numeral i.val, numeral_mem_omega _, ∅, ⟨?_, rfl⟩, rfl⟩
    rw [cutoff_denoteIn count i.val (.bv 0 : Tm 1) U ρ _ rfl,
      (code_eq_zero_iff count i.val).2 i.isLt]
    rfl

theorem canonical_denoteIn {count k : ℕ} (i : Fin count) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) (β : Fin k → ZFSet.{u}) :
    (canonical i : Tm k).denoteIn U ρ β = SetSem.pair (numeral i.val) ∅ := by
  suffices hn : (Encoding.Object.UnitVector.numeral i.val : Tm k).denoteIn U ρ β = numeral i.val by
    simpa only [canonical, Tm.denoteIn] using congrArg (fun a => SetSem.pair a ∅) hn
  generalize i.val = n
  induction n <;> simp_all [Encoding.Object.UnitVector.numeral, Tm.denoteIn, numeral,
    Silmaril.Logic.SetTheory.succ]

/-- Exact finite-tag correspondence, for every supplied universe interpretation. -/
noncomputable def semanticEquiv (count : ℕ) (U : ℕ → ZFSet.{u})
    (ρ : String → ZFSet.{u}) : Fin count ≃ ((Tag count : Tm 0).denoteIn U ρ Fin.elim0) :=
  Equiv.ofBijective
    (fun i => ⟨SetSem.pair (numeral i.val) ∅, (mem_denoteIn_iff count U ρ _).2 ⟨i, rfl⟩⟩)
    ⟨by
      intro i j h
      apply Fin.ext
      exact numeral_injective (ZFSet.pair_inj.1 (congrArg Subtype.val h)).1,
    by
      intro p
      obtain ⟨i, hi⟩ := (mem_denoteIn_iff count U ρ p.val).1 p.property
      exact ⟨i, Subtype.ext hi.symm⟩⟩

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.Object.FiniteTag
