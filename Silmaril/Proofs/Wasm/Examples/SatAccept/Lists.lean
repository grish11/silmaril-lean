module

public import Silmaril.Wasm.Examples.SatAccept.Defs
public import Silmaril.Logic.SAT.Carrier.Thms
public import Silmaril.Logic.SAT.CNF.Thms
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.Arith.Thms

/-!
# The SAT acceptor: what the loops compute

The running values of the loops (`modelPre`, `streamRun`, `clauseOk`) one word at a time, and
their final values as `satStream` and `satNested`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.SatAccept
open Silmaril.Logic.SAT Silmaril.Logic.SAT.Carrier
open Silmaril.Wasm.Numerics (bool32)

theorem bool32_or (a b : Bool) : bool32 a ||| bool32 b = bool32 (a || b) := by
  cases a <;> cases b <;> decide

theorem bool32_beq_zero (b : Bool) : (bool32 b == 0) = !b := by
  cases b <;> decide

theorem bool32_eq_zero_decide (b : Bool) : decide (bool32 b = 0) = !b := by
  cases b <;> decide

theorem modelPre_zero (M : List S32) : modelPre M 0 = true := by
  simp [modelPre]

theorem beq_comm32 (a b : S32) : (a == b) = (b == a) := by
  exact Bool.eq_iff_iff.2 (by rw [beq_iff_eq, beq_iff_eq]; exact eq_comm)

theorem modelPre_succ {M : List S32} {i : Nat} (h : i < M.length) :
    modelPre M (i + 1) =
      (modelPre M i && (LitWord (M[i]?.getD 0) && !M.contains (-(M[i]?.getD 0)))) := by
  simp only [modelPre, List.take_add_one, List.getElem?_eq_getElem h, Option.getD_some,
    Option.toList_some, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem contains_take_zero (M : List S32) (y : S32) : (M.take 0).contains y = false := by
  simp

theorem contains_take_succ {M : List S32} {j : Nat} (h : j < M.length) (y : S32) :
    (M.take (j + 1)).contains y = ((M.take j).contains y || (M[j]?.getD 0 == y)) := by
  simp only [List.take_add_one, List.getElem?_eq_getElem h, Option.getD_some, Option.toList_some,
    List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false, beq_comm32 y]

theorem any_take_succ {C : List S32} {k : Nat} (h : k < C.length) (p : S32 → Bool) :
    (C.take (k + 1)).any p = ((C.take k).any p || p (C[k]?.getD 0)) := by
  simp only [List.take_add_one, List.getElem?_eq_getElem h, Option.getD_some, Option.toList_some,
    List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem all_take_succ {α : Type} {C : List α} {k : Nat} (h : k < C.length) (d : α)
    (p : α → Bool) : (C.take (k + 1)).all p = ((C.take k).all p && p (C[k]?.getD d)) := by
  simp only [List.take_add_one, List.getElem?_eq_getElem h, Option.getD_some, Option.toList_some,
    List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem mem_take_succ_bool {M : List S32} {j : Nat} (h : j < M.length) (y : S32) :
    (decide (y ∈ M.take j) || (M[j]?.getD 0 == y)) = decide (y ∈ M.take (j + 1)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.take_add_one,
    List.getElem?_eq_getElem h, Option.getD_some, Option.toList_some, List.mem_append,
    List.mem_singleton]
  exact or_congr Iff.rfl eq_comm

theorem streamRun_nil (M : List S32) : streamRun M [] = (true, false) := rfl

theorem streamRun_snoc (M xs : List S32) (x : S32) :
    streamRun M (xs ++ [x]) = streamStep M (streamRun M xs) x := by
  simp [streamRun, List.foldl_append]

theorem streamRun_take_succ {M P : List S32} {i : Nat} (h : i < P.length) :
    streamRun M (P.take (i + 1)) = streamStep M (streamRun M (P.take i)) (P[i]?.getD 0) := by
  simp only [List.take_add_one, List.getElem?_eq_getElem h, Option.getD_some, Option.toList_some,
    streamRun_snoc]

theorem exists_toInt_eq (M : List S32) (x : S32) : (∃ a ∈ M, a.toInt = x.toInt) ↔ x ∈ M :=
  ⟨fun ⟨_, ha, e⟩ => BitVec.toInt_inj.1 e ▸ ha, fun h => ⟨x, h, rfl⟩⟩

theorem contains_map_toInt (M : List S32) (x : S32) :
    (M.map BitVec.toInt).contains x.toInt = M.contains x := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.toInt_inj]

theorem streamRun_eq (M xs : List S32) : streamRun M xs =
    (xs.all (· != BitVec.intMin 32) &&
      (Dimacs.cnf (xs.map BitVec.toInt)).all (·.any (M.map BitVec.toInt).contains),
     (Dimacs.pending (xs.map BitVec.toInt)).any (M.map BitVec.toInt).contains) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [streamRun_snoc, ih]
    by_cases hx : x = 0
    · subst hx
      simp [streamStep, Dimacs.cnf_snoc_zero, Dimacs.pending_snoc_zero, List.all_append,
        Bool.and_assoc, show (0#32 != BitVec.intMin 32) = true by decide]
    · have hx' : x.toInt ≠ 0 := by
        intro h; apply hx; exact BitVec.toInt_inj.1 (by simpa using h)
      simp [streamStep, show x ≠ 0#32 from hx, Dimacs.cnf_snoc_ne _ hx',
        Dimacs.pending_snoc_ne _ hx', List.all_append, List.any_append, exists_toInt_eq,
        Bool.and_comm, Bool.and_left_comm]

theorem modelPre_length (M : List S32) : modelPre M M.length =
    (M.all LitWord && (M.map BitVec.toInt).all fun l => !(M.map BitVec.toInt).contains (-l)) := by
  have key : ∀ x : S32, LitWord x = true →
      (M.map BitVec.toInt).contains (-x.toInt) = M.contains (-x) := by
    intro x hx
    have hne : x ≠ BitVec.intMin 32 := by
      simp only [LitWord, Bool.and_eq_true, bne_iff_ne, ne_eq] at hx; exact hx.2
    rw [← BitVec.toInt_neg_of_ne_intMin hne, contains_map_toInt]
  simp only [modelPre, List.take_length]
  by_cases hL : M.all LitWord = true
  · have hL' := List.all_eq_true.1 hL
    rw [hL, Bool.true_and, List.all_map, Bool.eq_iff_iff]
    simp only [List.all_eq_true, Function.comp_apply, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · intro h x hx; rw [key x (hL' x hx)]; exact (h x hx).2
    · intro h x hx; refine ⟨hL' x hx, ?_⟩; rw [← key x (hL' x hx)]; exact h x hx
  · rw [Bool.not_eq_true] at hL
    rw [hL, Bool.false_and, Bool.eq_false_iff]
    intro h
    have : M.all LitWord = true := List.all_eq_true.2 fun x hx => by
      have := List.all_eq_true.1 h x hx
      simp only [Bool.and_eq_true] at this
      exact this.1
    rw [hL] at this; cases this

set_option linter.unusedSimpArgs false in
theorem satStream_eq (P M : List S32) : satStream P M =
    (modelPre M M.length && (streamRun M P).1 && P.getLast?.all (· == 0)) := by
  rw [streamRun_eq, modelPre_length]
  unfold satStream decodeStream modelOk StreamOk
  cases h1 : P.all (· != BitVec.intMin 32) <;> cases h2 : P.getLast?.all (· == 0) <;>
    simp [h1, h2, Bool.and_assoc]

theorem satNested_eq (N : List (List S32)) (M : List S32) :
    satNested N M = (modelPre M M.length && N.all (clauseOk M)) := by
  rw [modelPre_length]
  unfold satNested decodeNested modelOk
  by_cases h : N.all (·.all LitWord) = true
  · simp only [h, ↓reduceIte]
    have hc : N.all (clauseOk M) = N.all (·.any M.contains) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true, clauseOk, Bool.and_eq_true]
      have h' := List.all_eq_true.1 h
      exact ⟨fun H c hc => (H c hc).2, fun H c hc => ⟨List.all_eq_true.1 (h' c hc), H c hc⟩⟩
    have hm : (N.map (·.map BitVec.toInt)).all (·.any (M.map BitVec.toInt).contains) =
        N.all (·.any M.contains) := by
      rw [List.all_map]
      congr 1; funext c
      simp only [Function.comp_apply, List.any_map]
      congr 1; funext x
      exact contains_map_toInt M x
    simp only [hc, hm, Bool.and_assoc]
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    symm
    rw [Bool.eq_false_iff]
    intro H
    rw [Bool.and_eq_true] at H
    have : N.all (·.all LitWord) = true := List.all_eq_true.2 fun c hc => by
      have := List.all_eq_true.1 H.2 c hc
      simp only [clauseOk, Bool.and_eq_true] at this
      exact this.1
    rw [h] at this; cases this

theorem getLast?_words (B : ByteArray) (p n : Nat) :
    (words B p n).getLast?.all (· == 0) = (n == 0 || wd B (p + 4 * (n - 1)) == 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [words]
  · rw [List.getLast?_eq_getElem?, length_words, getElem?_words (by omega)]
    simp [show n ≠ 0 by omega]

/-- The answer of `check-stream` as the loops compute it. -/
theorem stream_answer (B : ByteArray) (pp pl mp ml : Nat) :
    satStream (wordsAt B pp pl) (wordsAt B mp ml) =
      (modelPre (wordsAt B mp ml) ml && (streamRun (wordsAt B mp ml) ((wordsAt B pp pl).take pl)).1 &&
        (pl == 0 || wd B (pp + 4 * (pl - 1)) == 0)) := by
  rw [satStream_eq, getLast?_words, length_words, List.take_of_length_le (by simp)]

@[simp] theorem length_nestedAt (B : ByteArray) (p n : Nat) : (nestedAt B p n).length = n := by
  simp [nestedAt, Silmaril.Wasm.Acceptor.nestedAt]

theorem getD_nestedAt {B : ByteArray} {p n i : Nat} (h : i < n) :
    (nestedAt B p n)[i]?.getD [] =
      wordsAt B (wd B (p + 8 * i)).toNat (wd B (p + 8 * i + 4)).toNat := by
  simp [nestedAt, Silmaril.Wasm.Acceptor.nestedAt, h]

end Silmaril.Proofs.Wasm.Examples.SatAccept
