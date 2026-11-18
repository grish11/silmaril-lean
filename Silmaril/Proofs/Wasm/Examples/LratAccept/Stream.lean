module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Reset

@[expose] public section

/-!
# `check-stream`, every run

`stream_hwp`: from any LRAT view, with the problem `[pp, pp + 4 pl)` and the certificate
`[cp, cp + 4 cl)` in the ABI memory `B₁`, every run of the body of `check-stream` returns one
value, and a nonzero value only if the problem is in `UnsatStream` and the certificate words
decode (`LratStream.decode`). The reset gives `Good []`;
the feeding loop sends every problem word to `add_lit`, so the view satisfies `Good` for the
stream of the problem's words, while the flag `ok` records "no `Int32.MIN` so far"; the
termination test adds "empty or ending in `0`", and `cert_hwp` does the rest.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Examples.LratAccept
open Silmaril.Logic.SAT Silmaril.Logic.SAT.Carrier

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

/-! ## Words of the ABI memory -/

/-- The first `n` words at `p` are not `Int32.MIN`. -/
def OkUpTo (B : ByteArray) (p n : Nat) : Prop :=
  ∀ m, m < n → Silmaril.Wasm.Logic.Words.wd B (p + 4 * m) ≠ BitVec.ofNat 32 2147483648

instance (B : ByteArray) (p n : Nat) : Decidable (OkUpTo B p n) :=
  inferInstanceAs (Decidable (∀ m, m < n → _))

theorem okUpTo_zero {B : ByteArray} {p : Nat} : OkUpTo B p 0 := fun _ h => absurd h (by omega)

theorem okUpTo_succ {B : ByteArray} {p n : Nat} :
    OkUpTo B p n ∧ Silmaril.Wasm.Logic.Words.wd B (p + 4 * n) ≠ BitVec.ofNat 32 2147483648 ↔
      OkUpTo B p (n + 1) := by
  constructor
  · rintro ⟨h, hn⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact h m hm
    · exact hn
  · intro h
    exact ⟨fun m hm => h m (by omega), h n (by omega)⟩

theorem mem_wordsAt {B : ByteArray} {p n : Nat} {w : BitVec 32} :
    w ∈ wordsAt B p n ↔ ∃ m < n, Silmaril.Wasm.Logic.Words.wd B (p + 4 * m) = w := by
  simp [wordsAt, Silmaril.Wasm.Logic.Words.words]

theorem intMin_eq : BitVec.intMin 32 = BitVec.ofNat 32 2147483648 := by decide

/-- A well-formed stream in memory. -/
theorem streamOk_wordsAt {B : ByteArray} {p n : Nat} (hok : OkUpTo B p n)
    (hlast : 0 < n → Silmaril.Wasm.Logic.Words.wd B (p + 4 * (n - 1)) = 0#32) :
    StreamOk (wordsAt B p n) = true := by
  unfold StreamOk
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_wordsAt.1 hw
    have := hok m hm
    rw [intMin_eq]
    simpa using this
  · cases n with
    | zero => simp [wordsAt_zero]
    | succ n =>
      rw [wordsAt_succ, List.getLast?_append_of_ne_nil _ (by simp)]
      have := hlast (by omega)
      simp only [Nat.add_sub_cancel] at this
      simp [this]

theorem mem_unsatStream {B : ByteArray} {p n : Nat} (hok : OkUpTo B p n)
    (hlast : 0 < n → Silmaril.Wasm.Logic.Words.wd B (p + 4 * (n - 1)) = 0#32)
    (hu : (Dimacs.cnf ((wordsAt B p n).map BitVec.toInt)).Unsat) : wordsAt B p n ∈ UnsatStream :=
  ⟨_, by simp [decodeStream, streamOk_wordsAt hok hlast], hu⟩

theorem b32_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : b32 p = b32 q := by
  unfold b32; by_cases hp : p <;> simp_all

/-! ## Rules -/

variable {s : Store H} {G : List (BitVec 32)} {B B₁ : ByteArray} {L : List (BitVec 32)}
  {rs : List Val} {rest : List Admin} {Q : Post H}

/-- `i32.load` from the ABI memory at a known address. -/
theorem w_load1' (hS : Shape X s G B) (hA : Abi X B₁) {a : BitVec 32} {n : Nat}
    (ha : a.toNat = n) (hb : n + 4 ≤ B₁.size)
    (h : HWP P host s (fr X.mi L)
      (vals (Val.i32 (Silmaril.Wasm.Logic.Words.wd B₁ n) :: rs).reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 a :: rs).reverse ++ .plain ld1 :: rest) Q := by
  subst ha
  exact w_load1 hS hA hb h

/-- Normalise literal frames. -/
macro "lnorm" : tactic => `(tactic| try simp only [List.getD_cons_succ, List.getD_cons_zero,
  List.set_cons_succ, List.set_cons_zero])

/-- The feeding loop's invariant. -/
def SInv (X : Fix H) (B₁ : ByteArray) (pp pl cp cl : BitVec 32) : Store H → Frame → Prop :=
  fun s f => ∃ i x ok : BitVec 32,
    InvX X ((wordsAt B₁ pp.toNat i.toNat).map BitVec.toInt) s ∧
    f = fr X.mi [pp, pl, cp, cl, i, x, ok, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧ i.toNat ≤ pl.toNat ∧
    ok = b32 (OkUpTo B₁ pp.toNat i.toNat)

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **`check-stream`, every run.** -/
theorem stream_hwp (hX : MiOk X) (hC : CallsOk P host X) (hA : Abi X B₁) (hS : Shape X s G B)
    {pp pl cp cl : BitVec 32} (hpp : pp.toNat + 4 * pl.toNat ≤ B₁.size)
    (hcp : cp.toNat + 4 * cl.toNat ≤ B₁.size) :
    HWP P host s (fr X.mi [pp, pl, cp, cl, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
      (vals ([] : List Val).reverse ++ expression checkStreamBody ++ [])
      (bodyPost 1 (checkPost (H := H) (wordsAt B₁ pp.toNat pl.toNat ∈ UnsatStream ∧
        (LratStream.decode (wordsAt B₁ cp.toNat cl.toNat)).isSome = true))) := by
  have hsz := hA.size
  unfold checkStreamBody
  simp only [expression, List.map_append, List.append_assoc]
  rw [← List.append_assoc]
  refine reset_hwp hX hS fun s₁ B₀ hS₁ hG₁ => ?_
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  wstep; lnorm
  wstep; lnorm
  wstep; lnorm
  wstep; lnorm
  refine w_while (Inv := SInv X B₁ pp pl cp cl)
    ⟨0#32, 0#32, 1#32, by rw [show (0#32).toNat = 0 from rfl, wordsAt_zero]; exact ⟨_, _, hS₁, hG₁⟩,
      rfl, by simp, (b32_pos okUpTo_zero).symm⟩ ?_
  rintro s f ⟨i, x, ok, hI, rfl, hi, rfl⟩
  simp only [streamLoopBody, expression, List.map_cons, List.map_nil]
  wstep; lnorm
  wstep; lnorm
  wstep
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · -- the end of the problem: the termination test, then the certificate
    have hie : i.toNat = pl.toNat := by have := b32_ne_zero.1 hx; omega
    refine w_br (whilePost_exit ?_)
    wstep; lnorm
    wstep
    wstep
    refine w_if (rs := []) (fun hc => ?_) (fun hc => ?_)
    · have hpl : pl ≠ BitVec.ofNat 32 0 := b32_ne_zero.1 hc
      simp only [expression, List.map_cons, List.map_nil]
      obtain ⟨G₁, B₂, hS₂, hG₂⟩ := hI
      wstep; lnorm
      wstep; lnorm
      wstep; lnorm
      wstep
      wstep
      wstep
      wstep
      wstep
      refine w_load1' hS₂ hA (n := pp.toNat + 4 * (pl.toNat - 1)) (by bv_omega) (by bv_omega) ?_
      refine w_eqz' ?_
      refine w_and ?_
      rw [b32_and]
      refine w_lset (by simp) (by decide) ?_
      lnorm
      refine w_armEnd ?_
      rw [← List.append_assoc]
      refine cert_hwp hC hA hcp ⟨G₁, B₂, hS₂, hG₂⟩ fun ⟨hok, hlast⟩ hu hd => ?_
      rw [hie] at hok hu
      exact ⟨mem_unsatStream hok (fun _ => hlast) hu, hd⟩
    · have hpl : pl = BitVec.ofNat 32 0 := by have := b32_eq_zero.1 hc; simpa using this
      rw [← List.append_assoc]
      refine cert_hwp hC hA hcp hI fun hok hu hd => ?_
      rw [hie] at hok hu
      exact ⟨mem_unsatStream hok (fun h => absurd h (by rw [hpl]; simp)) hu, hd⟩
  · -- one more word
    have hlt : i.toNat < pl.toNat := by have := b32_eq_zero.1 hx; omega
    obtain ⟨G₁, B₂, hS₂, hG₂⟩ := hI
    wstep; lnorm
    wstep; lnorm
    wstep
    wstep
    wstep
    refine w_load1' hS₂ hA (n := pp.toNat + 4 * i.toNat) (by bv_omega) (by omega) ?_
    refine w_lset (by simp) (by decide) ?_
    lnorm
    wstep; lnorm
    refine w_addLit hC ⟨G₁, B₂, hS₂, hG₂⟩ fun s' hI' => ?_
    wstep; lnorm
    wstep; lnorm
    wstep
    wstep
    wstep
    rw [b32_and]
    refine w_lset (by simp) (by decide) ?_
    lnorm
    wstep; lnorm
    wstep
    wstep
    refine w_lset (by simp) (by decide) ?_
    lnorm
    have hi1 : (i + BitVec.ofNat 32 1).toNat = i.toNat + 1 := by bv_omega
    refine w_br (whilePost_cont ⟨i + BitVec.ofNat 32 1, _, _, ?_, rfl, by omega, ?_⟩)
    · rw [hi1, wordsAt_succ, List.map_append]
      simpa using hI'
    · rw [hi1]
      exact b32_congr okUpTo_succ

end Silmaril.Proofs.Wasm.Examples.LratAccept
