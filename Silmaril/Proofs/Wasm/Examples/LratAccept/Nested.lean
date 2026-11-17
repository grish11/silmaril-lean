module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Stream
public import Silmaril.Logic.SAT.Carrier.Thms

@[expose] public section

/-!
# `check-nested`, every run

`nested_hwp`: from any LRAT view, with the `pl` pairs `(ptr, len)` at `pp` and their blocks
(`NestedIn`) and the certificate `[cp, cp + 4 cl)` in the ABI memory `B₁`, every run of the
body of `check-nested` returns one value, and a nonzero value only if the problem
`nestedAt B₁ pp pl` is in `UnsatNested` and the certificate words decode. The reset gives `Good []`; the two feeding loops send
every word of every clause to `add_lit` and close each clause with `end_clause`, so the view
satisfies `Good` for `flatten` of the problem, while the flag `ok` records "only literal words
so far"; `cert_hwp` does the rest, and `decodeStream_flatten` relates the two readings.

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

local notation "W" => Silmaril.Wasm.Logic.Words.wd

/-! ## Clauses of the ABI memory -/

/-- The first `n` words at `p` are literal words. -/
def ClOk (B : ByteArray) (p n : Nat) : Prop :=
  ∀ m, m < n → W B (p + 4 * m) ≠ BitVec.ofNat 32 0 ∧ W B (p + 4 * m) ≠ BitVec.ofNat 32 2147483648

instance (B : ByteArray) (p n : Nat) : Decidable (ClOk B p n) :=
  inferInstanceAs (Decidable (∀ m, m < n → _))

/-- The pointer and the length of clause `c`. -/
def cpOf (B : ByteArray) (pp c : Nat) : Nat := (W B (pp + 8 * c)).toNat
def lenOf (B : ByteArray) (pp c : Nat) : Nat := (W B (pp + 8 * c + 4)).toNat

/-- The first `i` clauses consist of literal words. -/
def NestOk (B : ByteArray) (pp i : Nat) : Prop := ∀ c, c < i → ClOk B (cpOf B pp c) (lenOf B pp c)

instance (B : ByteArray) (pp i : Nat) : Decidable (NestOk B pp i) :=
  inferInstanceAs (Decidable (∀ c, c < i → _))

theorem clOk_succ {B : ByteArray} {p n : Nat} :
    ClOk B p n ∧ (W B (p + 4 * n) ≠ BitVec.ofNat 32 0 ∧ W B (p + 4 * n) ≠ BitVec.ofNat 32 2147483648) ↔
      ClOk B p (n + 1) := by
  constructor
  · rintro ⟨h, hn⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact h m hm
    · exact hn
  · intro h
    exact ⟨fun m hm => h m (by omega), h n (by omega)⟩

theorem nestOk_succ {B : ByteArray} {pp i : Nat} :
    NestOk B pp i ∧ ClOk B (cpOf B pp i) (lenOf B pp i) ↔ NestOk B pp (i + 1) := by
  constructor
  · rintro ⟨h, hn⟩ c hc
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact h c hc
    · exact hn
  · intro h
    exact ⟨fun c hc => h c (by omega), h i (by omega)⟩

theorem nestedAt_succ {B : ByteArray} {pp n : Nat} :
    nestedAt B pp (n + 1) = nestedAt B pp n ++ [wordsAt B (cpOf B pp n) (lenOf B pp n)] := by
  simp [nestedAt, Silmaril.Wasm.Acceptor.nestedAt, cpOf, lenOf, List.range_succ]

theorem nestedAt_zero {B : ByteArray} {pp : Nat} : nestedAt B pp 0 = [] := by
  simp [nestedAt, Silmaril.Wasm.Acceptor.nestedAt]

theorem flatten_append (p q : Nested) : flatten (p ++ q) = flatten p ++ flatten q := by
  simp [flatten]

theorem flatten_single (c : List S32) : flatten [c] = c ++ [0] := by
  simp [flatten]

theorem allLit_of_nestOk {B : ByteArray} {pp n : Nat} (h : NestOk B pp n) :
    (nestedAt B pp n).all (·.all LitWord) = true := by
  simp only [List.all_eq_true]
  intro c hc w hw
  simp only [nestedAt, Silmaril.Wasm.Acceptor.nestedAt, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  obtain ⟨m, hm, rfl⟩ := mem_wordsAt.1 hw
  have := h i hi m hm
  simp only [cpOf] at this
  simp only [LitWord, intMin_eq, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨this.1, this.2⟩

theorem mem_unsatNested {B : ByteArray} {pp n : Nat} (hok : NestOk B pp n)
    (hu : (Dimacs.cnf ((flatten (nestedAt B pp n)).map BitVec.toInt)).Unsat) :
    nestedAt B pp n ∈ UnsatNested := by
  have hd : decodeNested (nestedAt B pp n) = some ((nestedAt B pp n).map (·.map BitVec.toInt)) := by
    simp [decodeNested, allLit_of_nestOk hok]
  have h2 := (decodeStream_eq_some.1 (decodeStream_flatten hd)).2
  exact ⟨_, hd, h2 ▸ hu⟩

/-! ## The loops -/

variable {s : Store H} {G : List (BitVec 32)} {B B₁ : ByteArray}

/-- The clause loop's invariant. -/
def NInv (X : Fix H) (B₁ : ByteArray) (pp pl cp cl : BitVec 32) : Store H → Frame → Prop :=
  fun s f => ∃ i x ok a13 a14 a15 : BitVec 32,
    InvX X ((flatten (nestedAt B₁ pp.toNat i.toNat)).map BitVec.toInt) s ∧
    f = fr X.mi [pp, pl, cp, cl, i, x, ok, 0, 0, 0, 0, 0, 0, a13, a14, a15] ∧ i.toNat ≤ pl.toNat ∧
    ok = b32 (NestOk B₁ pp.toNat i.toNat)

/-- The literal loop's invariant, in clause `i` (at `cpi`, of `len` words). -/
def LInv (X : Fix H) (B₁ : ByteArray) (pp pl cp cl i cpi len : BitVec 32) : Store H → Frame → Prop :=
  fun s f => ∃ k x ok : BitVec 32,
    InvX X ((flatten (nestedAt B₁ pp.toNat i.toNat)).map BitVec.toInt ++
      (wordsAt B₁ cpi.toNat k.toNat).map BitVec.toInt) s ∧
    f = fr X.mi [pp, pl, cp, cl, i, x, ok, 0, 0, 0, 0, 0, 0, k, cpi, len] ∧ k.toNat ≤ len.toNat ∧
    ok = b32 (NestOk B₁ pp.toNat i.toNat ∧ ClOk B₁ cpi.toNat k.toNat)

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **`check-nested`, every run.** -/
theorem nested_hwp (hX : MiOk X) (hC : CallsOk P host X) (hA : Abi X B₁) (hS : Shape X s G B)
    {pp pl cp cl : BitVec 32} (hpp : NestedIn B₁ pp.toNat pl.toNat)
    (hcp : cp.toNat + 4 * cl.toNat ≤ B₁.size) :
    HWP P host s (fr X.mi [pp, pl, cp, cl, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
      (vals ([] : List Val).reverse ++ expression checkNestedBody ++ [])
      (bodyPost 1 (checkPost (H := H) (nestedAt B₁ pp.toNat pl.toNat ∈ UnsatNested ∧
        (LratStream.decode (wordsAt B₁ cp.toNat cl.toNat)).isSome = true))) := by
  have hsz := hA.size
  obtain ⟨hpp1, hpp2⟩ := hpp
  unfold checkNestedBody
  simp only [expression, List.map_append, List.append_assoc]
  rw [← List.append_assoc]
  refine reset_hwp hX hS fun s₁ B₀ hS₁ hG₁ => ?_
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  wstep; lnorm
  wstep; lnorm
  wstep; lnorm
  wstep; lnorm
  refine w_while (Inv := NInv X B₁ pp pl cp cl)
    ⟨0#32, 0#32, 1#32, 0#32, 0#32, 0#32,
      by rw [show (0#32).toNat = 0 from rfl, nestedAt_zero]; exact ⟨_, _, hS₁, hG₁⟩,
      rfl, by simp, (b32_pos (fun c hc => absurd hc (by simp))).symm⟩ ?_
  rintro s f ⟨i, x, ok, a13, a14, a15, hI, rfl, hi, rfl⟩
  simp only [clauseLoopBody, expression, List.map_cons, List.map_nil]
  wstep; lnorm
  wstep; lnorm
  wstep
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · -- all clauses fed: the certificate
    have hie : i.toNat = pl.toNat := by have := b32_ne_zero.1 hx; omega
    refine w_br (whilePost_exit ?_)
    rw [← List.append_assoc]
    refine cert_hwp hC hA hcp hI fun hok hu hd => ?_
    rw [hie] at hok hu
    exact ⟨mem_unsatNested hok hu, hd⟩
  · -- clause `i`
    have hlt : i.toNat < pl.toNat := by have := b32_eq_zero.1 hx; omega
    obtain ⟨G₁, B₂, hS₂, hG₂⟩ := hI
    have hcl := hpp2 i.toNat hlt
    wstep; lnorm
    wstep; lnorm
    wstep
    wstep
    wstep
    refine w_load1' hS₂ hA (n := pp.toNat + 8 * i.toNat) (by bv_omega) (by omega) ?_
    refine w_lset (by simp) (by decide) ?_
    lnorm
    wstep; lnorm
    wstep; lnorm
    wstep
    wstep
    wstep
    wstep
    wstep
    refine w_load1' hS₂ hA (n := pp.toNat + 8 * i.toNat + 4) (by bv_omega) (by omega) ?_
    refine w_lset (by simp) (by decide) ?_
    lnorm
    wstep
    refine w_lset (by simp) (by decide) ?_
    lnorm
    -- the words of the clause
    refine w_while (Inv := LInv X B₁ pp pl cp cl i (W B₁ (pp.toNat + 8 * i.toNat))
        (W B₁ (pp.toNat + 8 * i.toNat + 4)))
      ⟨0#32, x, _, by rw [show (BitVec.ofNat 32 0).toNat = 0 from rfl, wordsAt_zero,
          List.map_nil, List.append_nil]; exact ⟨G₁, B₂, hS₂, hG₂⟩,
        rfl, by simp, b32_congr ⟨fun h => ⟨h, fun m hm => absurd hm (by simp)⟩, fun h => h.1⟩⟩ ?_
    rintro s' f' ⟨k, x', ok', hI', rfl, hk, rfl⟩
    simp only [litLoopBody, expression, List.map_cons, List.map_nil]
    wstep; lnorm
    wstep; lnorm
    wstep
    refine w_brIf (fun hx' => ?_) (fun hx' => ?_)
    · -- the end of the clause: `end_clause`, next clause
      have hke : k.toNat = (W B₁ (pp.toNat + 8 * i.toNat + 4)).toNat := by
        have := b32_ne_zero.1 hx'; omega
      refine w_br (whilePost_exit ?_)
      refine w_endClause (rs := []) hC hI' fun s'' hI'' => ?_
      wstep; lnorm
      wstep
      wstep
      refine w_lset (by simp) (by decide) ?_
      lnorm
      have hi1 : (i + BitVec.ofNat 32 1).toNat = i.toNat + 1 := by bv_omega
      refine w_br (whilePost_cont ⟨i + BitVec.ofNat 32 1, _, _, _, _, _, ?_, rfl, by omega, ?_⟩)
      · rw [hi1, nestedAt_succ, flatten_append, flatten_single, List.map_append, List.map_append]
        rw [hke] at hI''
        simpa [cpOf, lenOf, List.append_assoc] using hI''
      · rw [hi1]
        refine b32_congr ?_
        rw [← nestOk_succ, hke]
        rfl
    · -- one more word
      have hlt' : k.toNat < (W B₁ (pp.toNat + 8 * i.toNat + 4)).toNat := by
        have := b32_eq_zero.1 hx'; omega
      obtain ⟨G₃, B₃, hS₃, hG₃⟩ := hI'
      wstep; lnorm
      wstep; lnorm
      wstep
      wstep
      wstep
      refine w_load1' hS₃ hA (n := (W B₁ (pp.toNat + 8 * i.toNat)).toNat + 4 * k.toNat)
        (by bv_omega) (by omega) ?_
      refine w_lset (by simp) (by decide) ?_
      lnorm
      wstep; lnorm
      refine w_addLit hC ⟨G₃, B₃, hS₃, hG₃⟩ fun s'' hI'' => ?_
      wstep; lnorm
      wstep; lnorm
      wstep
      wstep
      wstep; lnorm
      wstep
      wstep
      wstep
      wstep
      rw [b32_and, b32_and]
      refine w_lset (by simp) (by decide) ?_
      lnorm
      wstep; lnorm
      wstep
      wstep
      refine w_lset (by simp) (by decide) ?_
      lnorm
      have hk1 : (k + BitVec.ofNat 32 1).toNat = k.toNat + 1 := by bv_omega
      refine w_br (whilePost_cont ⟨k + BitVec.ofNat 32 1, _, _, ?_, rfl, by omega, ?_⟩)
      · rw [hk1, wordsAt_succ, List.map_append, ← List.append_assoc]
        simpa using hI''
      · rw [hk1]
        refine b32_congr ?_
        rw [← clOk_succ]
        tauto

end Silmaril.Proofs.Wasm.Examples.LratAccept
