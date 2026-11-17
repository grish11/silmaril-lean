module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.DispatchVal

@[expose] public section

/-!
# The certificate loop and the answer

`cert_hwp`: from a store whose LRAT view satisfies `Good xs` (`InvX X xs`), with the
"well-formed problem" flag `b32 p` in local `6` and `0` in local `8`, every run of `certCode`
returns one value `r`, and `r ≠ 0` only if `p` holds, the formula of `xs` is unsatisfiable and
the certificate words decode (`LratStream.decode`). The certificate words are read from the ABI
memory (in bounds); whatever they are, the dispatch keeps `InvX X xs` and computes the parser
automaton (`dispatch_val`), so the answer of `unsat()` is sound and local `7` is `certRun 0` of
the words read so far; the answer needs it to be `0`, and `decode_of_certRun` concludes.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Logic.SAT

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

/-- The postcondition of a check body: one result, nonzero only if `Goal`. -/
def checkPost (Goal : Prop) : Store H → Outcome → Prop :=
  fun _ o => ∀ r : BitVec 32, o = .normal [Val.i32 r] → r ≠ 0#32 → Goal

/-- The fixed locals of the certificate loop: `cp`, the flag, the answer `0`, the bound `n`. -/
def CJ (cp ok n : BitVec 32) (L : List (BitVec 32)) : Prop :=
  L.getD 2 0 = cp ∧ L.getD 6 0 = ok ∧ L.getD 8 0 = 0#32 ∧ L.getD 12 0 = n

/-- The loop invariant: local `7` is the parser state after the words read so far. -/
def CertInv (X : Fix H) (xs : List Int) (B₁ : ByteArray) (cp ok n : BitVec 32) :
    Store H → Frame → Prop :=
  fun s f => InvX X xs s ∧ ∃ L, f = fr X.mi L ∧ L.length = 16 ∧ CJ cp ok n L ∧
    (L.getD 4 0).toNat ≤ n.toNat ∧
    L.getD 7 0 = BitVec.ofNat 32 (certRun 0 (wordsAt B₁ cp.toNat (L.getD 4 0).toNat))

theorem CJ.set {cp ok n : BitVec 32} {L : List (BitVec 32)} (h : CJ cp ok n L) {k : Nat}
    (hk : k ≠ 2 ∧ k ≠ 6 ∧ k ≠ 8 ∧ k ≠ 12) (v : BitVec 32) : CJ cp ok n (L.set k v) := by
  obtain ⟨h2, h6, h8, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getD_set_ne (Ne.symm (Ne.symm hk.1))]; exact h2
  · rw [getD_set_ne hk.2.1]; exact h6
  · rw [getD_set_ne hk.2.2.1]; exact h8
  · rw [getD_set_ne hk.2.2.2]; exact h12

theorem and_ne_zero {a b : BitVec 32} (h : a &&& b ≠ 0#32) : a ≠ 0#32 ∧ b ≠ 0#32 := by
  constructor <;> rintro rfl <;> simp at h

theorem wordsAt_succ {B : ByteArray} {p n : Nat} :
    wordsAt B p (n + 1) = wordsAt B p n ++ [Silmaril.Wasm.Logic.Words.wd B (p + 4 * n)] := by
  simp [wordsAt, Silmaril.Wasm.Logic.Words.words, List.range_succ]

theorem wordsAt_zero {B : ByteArray} {p : Nat} : wordsAt B p 0 = [] := by
  simp [wordsAt, Silmaril.Wasm.Logic.Words.words]

/-- A parser state `≤ 9` that is `0` as a word is `0`. -/
theorem certRun_eq_zero {ws : List (BitVec 32)} (h : BitVec.ofNat 32 (certRun 0 ws) = 0#32) :
    certRun 0 ws = 0 := by
  have hle := certRun_le (q := 0) (by omega) ws
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  simpa using this

variable {s : Store H} {xs : List Int} {B₁ : ByteArray}

set_option maxHeartbeats 4000000 in
/-- **The certificate loop and the answer.** -/
theorem cert_hwp (hC : CallsOk P host X) (hA : Abi X B₁)
    {pp pl cp cl a4 a5 a7 a9 a10 a11 a12 a13 a14 a15 : BitVec 32}
    (hcp : cp.toNat + 4 * cl.toNat ≤ B₁.size) (hI : InvX X xs s) {p : Prop} [Decidable p]
    {Goal : Prop}
    (hgoal : p → (Dimacs.cnf xs).Unsat →
      (Silmaril.Logic.SAT.Carrier.LratStream.decode (wordsAt B₁ cp.toNat cl.toNat)).isSome = true →
        Goal) :
    HWP P host s (fr X.mi [pp, pl, cp, cl, a4, a5, b32 p, a7, 0, a9, a10, a11, a12, a13, a14, a15])
      (vals ([] : List Val).reverse ++ expression certCode ++ [])
      (bodyPost 1 (checkPost (H := H) Goal)) := by
  have hsz := hA.size
  have hn : (cl * b32 p).toNat ≤ cl.toNat := by
    rw [mul_b32]; split <;> simp
  simp only [certCode, expression, List.map_cons, List.map_nil, List.append_nil]
  wrun
  refine w_while (Inv := CertInv X xs B₁ cp (b32 p) (cl * b32 p))
    ⟨hI, _, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, by simp, by simp [wordsAt_zero, certRun_nil]⟩ ?_
  rintro s f ⟨hI, L, rfl, hL, hJ, hj, h7⟩
  simp only [certLoopBody, expression, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine w_lget (L := L) (by omega) (by decide) ?_
  refine w_lget (L := L) (by omega) (by decide) ?_
  refine w_geu ?_
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · -- the end of the certificate: the answer
    refine w_br (whilePost_exit ?_)
    obtain ⟨h2, h6, h8, h12⟩ := hJ
    obtain ⟨G, B, hS, hG⟩ := hI
    refine w_lget (L := L) (by omega) (by decide) ?_
    rw [h6]
    refine w_lget (L := L) (by omega) (by decide) ?_
    refine w_eqz' ?_
    refine w_and ?_
    rw [b32_and]
    refine w_if (rs := []) (fun hc => ?_) (fun hc => ?_)
    · obtain ⟨hp, h70⟩ := b32_ne_zero.1 hc
      have hcl : cl * b32 p = cl := by rw [mul_b32]; simp [hp]
      have hje : (L.getD 4 0).toNat = cl.toNat := by
        have := b32_ne_zero.1 hx; rw [h12, hcl] at this; rw [hcl] at hj; omega
      rw [h70, hje] at h7
      have hdec := decode_of_certRun (certRun_eq_zero h7.symm)
      simp only [expression, List.map_cons, List.map_nil]
      refine w_unsat (rs := []) hC ⟨G, B, hS, hG⟩ fun s' v hI' hu => ?_
      refine w_const ?_
      refine w_ne ?_
      refine w_lset (L := L) (by omega) (by decide) ?_
      refine w_armEnd ?_
      obtain ⟨G', B', hS', -⟩ := hI'
      refine w_const ?_
      refine w_gset8 hS' hA fun s'' => ?_
      refine w_lget (by simp [hL]) (by decide) ?_
      refine w_end ⟨rfl, fun r hr hr0 => ?_⟩
      rw [getD_set_self (by omega)] at hr
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, Outcome.normal.injEq,
        List.cons.injEq, and_true] at hr
      have hr' := Silmaril.Wasm.Logic.Hoare.i32_inj hr
      subst hr'
      exact hgoal hp (hu (b32_ne_zero.1 hr0)) hdec
    · refine w_const ?_
      refine w_gset8 hS hA fun s'' => ?_
      refine w_lget (L := L) (by omega) (by decide) ?_
      refine w_end ⟨rfl, fun r hr hr0 => ?_⟩
      rw [h8] at hr
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, Outcome.normal.injEq,
        List.cons.injEq, and_true] at hr
      have hr' := Silmaril.Wasm.Logic.Hoare.i32_inj hr
      subst hr'
      exact absurd rfl hr0
  · -- one more word
    have hlt : (L.getD 4 0).toNat < (cl * b32 p).toNat := by
      have := b32_eq_zero.1 hx; rw [hJ.2.2.2] at this; omega
    obtain ⟨G, B, hS, hG⟩ := hI
    have haddr : (L.getD 2 0 + L.getD 4 0 * BitVec.ofNat 32 4).toNat =
        cp.toNat + 4 * (L.getD 4 0).toNat := by
      rw [hJ.1]
      have h4 := hlt
      generalize L.getD 4 0 = j at h4 ⊢
      bv_omega
    refine w_lget (L := L) (by omega) (by decide) ?_
    refine w_lget (L := L) (by omega) (by decide) ?_
    refine w_const ?_
    refine w_mul ?_
    refine w_add ?_
    refine w_load1 hS hA ?_ ?_
    · rw [haddr]
      have h4 := hlt
      generalize L.getD 4 0 = j at h4 ⊢
      bv_omega
    rw [haddr]
    refine w_lset (L := L) (by omega) (by decide) ?_
    rw [← List.append_assoc]
    refine dispatch_val (J := fun L' => CJ cp (b32 p) (cl * b32 p) L' ∧
        L'.getD 4 0 = L.getD 4 0 ∧ (L.getD 4 0).toNat < (cl * b32 p).toNat)
      (x := Silmaril.Wasm.Logic.Words.wd B₁ (cp.toNat + 4 * (L.getD 4 0).toNat))
      (st := L.getD 7 0) hC ?_ _ _ ?_ s _
      ⟨⟨G, B, hS, hG⟩, _, rfl, by simp [hL],
        ⟨hJ.set (by omega) _, by rw [getD_set_ne (by omega)], hlt⟩,
        getD_set_self (by omega) _, by rw [getD_set_ne (by omega)]⟩
    · rintro L' k v hk ⟨hJ', h4', hlt'⟩
      unfold Writes at hk
      exact ⟨hJ'.set (by omega) v, by rw [getD_set_ne (by omega)]; exact h4', hlt'⟩
    · rintro s' f' ⟨hI', L', rfl, hL', ⟨hJ', h4', hlt'⟩, h7'⟩
      refine w_lget (L := L') (by omega) (by decide) ?_
      refine w_const ?_
      refine w_add ?_
      refine w_lset (L := L') (by omega) (by decide) ?_
      have hj1 : (L'.getD 4 0 + BitVec.ofNat 32 1).toNat = (L.getD 4 0).toNat + 1 := by
        rw [h4']
        have : (cl * b32 p).toNat < 2 ^ 31 := by omega
        generalize L.getD 4 0 = j at hlt' ⊢
        bv_omega
      refine w_br (whilePost_cont ⟨hI', _, rfl, by simp [hL'], hJ'.set (by omega) _, ?_, ?_⟩)
      · rw [getD_set_self (by omega), hj1]; omega
      · rw [getD_set_self (by omega), hj1, getD_set_ne (by omega), h7', h7,
          dispV_eq (certRun_le (by omega) _), wordsAt_succ, certRun_append]
        rfl

end Silmaril.Proofs.Wasm.Examples.LratAccept
