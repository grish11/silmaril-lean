module

public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

/-!
# Lowered lists in the memory of a bump allocator: proofs

`params_holds`: `LParams` from a store with heap pointer `t₀` ends in a store with heap pointer
`t₁ ≥ t₀`, the memory unchanged outside `[t₀, t₁)` and holding the arguments (`FlatHolds`). By
mutual recursion on the lowering derivations (`store_holds`, `list_holds`, `elems_holds`):

* an `s32` is one write at `p`;
* a list allocates a block at or above the heap pointer (`BumpAlloc.realloc`), stores its
  elements there (they lie below the new heap pointer, their own blocks above it), then writes
  its `(ptr, len)` pair at `p`, which lies below the old heap pointer;
* each step changes only its slot and the bytes between the old and the new heap pointer
  (`SameOutside2`), and what an earlier step established depends only on bytes it owns
  (`holds_frame`, `holdsL_frame`), so it survives (`Agree`).

`holdsL_words`: the elements of a `list<s32>` are the words of its block.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Numerics (Profile)

/-! ## Bytes -/

/-- `B'` has the bytes of `B` on `[a, b)`. -/
def Agree (B B' : ByteArray) (a b : Nat) : Prop :=
  ∀ i, a ≤ i → i < b → B'.data.toList[i]? = B.data.toList[i]?

theorem wd_agree {B B' : ByteArray} {a : Nat} (hs : B'.size = B.size)
    (h : Agree B B' a (a + 4)) : wd B' a = wd B a := by
  by_cases hB : a + 4 ≤ B.size
  · have hB' : a + 4 ≤ B'.size := hs ▸ hB
    have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, 4⟩ =
        Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, 4⟩ := by
      apply List.ext_getElem?
      intro i
      rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
      dsimp only
      split
      · exact h _ (by omega) (by omega)
      · rfl
    rw [wd, wd, Silmaril.Wasm.Logic.Core.load_eq hB, Silmaril.Wasm.Logic.Core.load_eq hB', hr]
  · have hl : Memory.load B a 4 = none := Silmaril.Wasm.Logic.Core.load_eq_none (by omega)
    have hl' : Memory.load B' a 4 = none :=
      Silmaril.Wasm.Logic.Core.load_eq_none (by rw [hs]; omega)
    rw [wd, wd, hl, hl']

theorem four_le_size (t : LTy) : 4 ≤ t.size := by cases t <;> simp [LTy.size]

theorem length_le_mul (t : LTy) (n : Nat) : n ≤ n * t.size :=
  Nat.le_mul_of_pos_right n (by have := four_le_size t; omega)

theorem memLen_eq (s : Store Nat) (ma : Nat) : memLen s ma = (memBytesOf s ma).size := by
  unfold memLen memBytesOf
  cases s.mems[ma]? <;> rfl

/-- A write of a word through `memWrite?`. -/
theorem memWrite_le32 {s s' : Store Nat} {ma p : Nat} {x : BitVec 32}
    (h : Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le32 x) = some s') :
    p + 4 ≤ (memBytesOf s ma).size ∧ memBytesOf s' ma = wr (memBytesOf s ma) p x := by
  obtain ⟨mi, b, hm, hw, rfl⟩ := Silmaril.Wasm.Component.Engine.Core3.memWrite?_eq_some h
  have hm' : memBytesOf s ma = mi.bytes := by simp [memBytesOf, hm]
  have hb : p + 4 ≤ mi.bytes.size := by
    unfold Memory.writeBytes at hw
    split at hw
    · rename_i hle
      simpa [le32] using hle
    · cases hw
  have hlt : ma < s.mems.length := (List.getElem?_eq_some_iff.mp hm).1
  have hw' : Memory.writeBytes mi.bytes p (le32 x) = some (wr mi.bytes p x) := store_wr x hb
  rw [hw'] at hw
  cases hw
  refine ⟨hm' ▸ hb, ?_⟩
  rw [hm']
  simp [memBytesOf, Store.setMem, List.getElem?_set_self hlt]

/-! ## Frames and widening of the readings -/

section
variable {B B' : ByteArray} {lo hi : Nat}

mutual
theorem holds_frame (hs : B'.size = B.size) (hag : Agree B B' lo hi) :
    ∀ (t : LTy) (v : LVal) (p : Nat), Agree B B' p (p + t.size) →
      Holds B lo hi t v p → Holds B' lo hi t v p
  | .s32, .s32 x, p, hp, h => by
    simp only [Holds] at h ⊢
    exact ⟨hs ▸ h.1, (wd_agree hs fun i h₁ h₂ => hp i h₁ (by simp only [LTy.size]; omega)).trans h.2⟩
  | .list t, .list vs, p, hp, h => by
    simp only [Holds] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have e0 : wd B' p = wd B p :=
      wd_agree hs fun i h₁ h₂ => hp i h₁ (by simp only [LTy.size]; omega)
    have e4 : wd B' (p + 4) = wd B (p + 4) :=
      wd_agree hs fun i h₁ h₂ => hp i (by omega) (by simp only [LTy.size]; omega)
    rw [e0, e4, hs]
    exact ⟨h1, h2, h3, h4, h5,
      holdsL_frame hs hag t vs _ (fun i h₁ h₂ => hag i (by omega) (by omega)) h6⟩
  | .s32, .list _, _, _, h => by simp [Holds] at h
  | .list _, .s32 _, _, _, h => by simp [Holds] at h

theorem holdsL_frame (hs : B'.size = B.size) (hag : Agree B B' lo hi) :
    ∀ (t : LTy) (vs : List LVal) (q : Nat), Agree B B' q (q + vs.length * t.size) →
      HoldsL B lo hi t vs q → HoldsL B' lo hi t vs q
  | _, [], _, _, _ => trivial
  | t, v :: vs, q, hq, h => by
    simp only [HoldsL] at h ⊢
    simp only [List.length_cons, Nat.succ_mul] at hq
    exact ⟨holds_frame hs hag t v q (fun i h₁ h₂ => hq i h₁ (by omega)) h.1,
      holdsL_frame hs hag t vs _ (fun i h₁ h₂ => hq i (by omega) (by omega)) h.2⟩
end

end

section
variable {B : ByteArray} {lo hi lo' hi' : Nat}

mutual
theorem holds_mono (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ (t : LTy) (v : LVal) (p : Nat), Holds B lo hi t v p → Holds B lo' hi' t v p
  | .s32, .s32 _, _, h => h
  | .list t, .list vs, p, h => by
    simp only [Holds] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, by omega, by omega, h5, holdsL_mono hl hh t vs _ h6⟩
  | .s32, .list _, _, h => by simp [Holds] at h
  | .list _, .s32 _, _, h => by simp [Holds] at h

theorem holdsL_mono (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ (t : LTy) (vs : List LVal) (q : Nat), HoldsL B lo hi t vs q → HoldsL B lo' hi' t vs q
  | _, [], _, _ => trivial
  | t, v :: vs, q, h => by
    simp only [HoldsL] at h ⊢
    exact ⟨holds_mono hl hh t v q h.1, holdsL_mono hl hh t vs _ h.2⟩
end

theorem flatHolds_mono (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ (ts : List LTy) (vs : List LVal) (fl : List Core.Val),
      FlatHolds B lo hi ts vs fl → FlatHolds B lo' hi' ts vs fl
  | [], [], _, h => h
  | .s32 :: ts, .s32 _ :: vs, _, h => by
    simp only [FlatHolds] at h ⊢
    obtain ⟨fl', rfl, h⟩ := h
    exact ⟨fl', rfl, flatHolds_mono hl hh ts vs fl' h⟩
  | .list t :: ts, .list us :: vs, _, h => by
    simp only [FlatHolds] at h ⊢
    obtain ⟨q, fl', rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨q, fl', rfl, h1, h2, by omega, by omega, h5, holdsL_mono hl hh t us q h6,
      flatHolds_mono hl hh ts vs fl' h7⟩
  | [], _ :: _, _, h => by simp [FlatHolds] at h
  | _ :: _, [], _, h => by simp [FlatHolds] at h
  | .s32 :: _, .list _ :: _, _, h => by simp [FlatHolds] at h
  | .list _ :: _, .s32 _ :: _, _, h => by simp [FlatHolds] at h

end

theorem flatHolds_frame {B B' : ByteArray} {lo hi : Nat} (hs : B'.size = B.size)
    (hag : Agree B B' lo hi) :
    ∀ (ts : List LTy) (vs : List LVal) (fl : List Core.Val),
      FlatHolds B lo hi ts vs fl → FlatHolds B' lo hi ts vs fl
  | [], [], _, h => h
  | .s32 :: ts, .s32 _ :: vs, _, h => by
    simp only [FlatHolds] at h ⊢
    obtain ⟨fl', rfl, h⟩ := h
    exact ⟨fl', rfl, flatHolds_frame hs hag ts vs fl' h⟩
  | .list t :: ts, .list us :: vs, _, h => by
    simp only [FlatHolds] at h ⊢
    obtain ⟨q, fl', rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨q, fl', rfl, h1, h2, h3, h4, hs ▸ h5,
      holdsL_frame hs hag t us q (fun i h₁ h₂ => hag i (by omega) (by omega)) h6,
      flatHolds_frame hs hag ts vs fl' h7⟩
  | [], _ :: _, _, h => by simp [FlatHolds] at h
  | _ :: _, [], _, h => by simp [FlatHolds] at h
  | .s32 :: _, .list _ :: _, _, h => by simp [FlatHolds] at h
  | .list _ :: _, .s32 _ :: _, _, h => by simp [FlatHolds] at h

/-! ## The lowering -/

section
variable {P : Profile} {ra ma N : Nat} {Inv : Store Nat → Nat → Prop}

mutual
theorem store_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {t : LTy} {v : LVal} {p : Nat} {s s' : Store Nat} {t₀ : Nat},
      LStore P ra ma t v p s s' → Inv s t₀ → p + t.size ≤ t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside2 (memBytesOf s ma) (memBytesOf s' ma) p t.size t₀ (t₁ - t₀) ∧
        Holds (memBytesOf s' ma) t₀ t₁ t v p
  | _, _, _, _, _, t₀, .s32 (x := x) hw, hi, _ => by
    obtain ⟨hb4, he⟩ := memWrite_le32 hw
    refine ⟨t₀, hb.write hi hw, Nat.le_refl _, ?_, ?_⟩
    · rw [he]
      exact (sameOutside_wr x hb4 (Nat.le_refl _) (by simp only [LTy.size]; omega)).two _ _
    · rw [he]
      simp only [Holds]
      exact ⟨by rw [size_wr x hb4]; exact hb4, wd_wr_same x hb4⟩
  | _, _, p, s, s', t₀, .list (t := t) (vs := vs) (s₁ := s₁) (s₂ := s₂) (q := q) hl hw₁ hw₂,
      hi, hp => by
    simp only [LTy.size] at hp ⊢
    obtain ⟨t₁, hi₁, h01, hso, h0q, hq1, hqB, hq32, hL⟩ := list_holds hb hl hi
    obtain ⟨hb₁, he₁⟩ := memWrite_le32 hw₁
    obtain ⟨hb₂, he₂⟩ := memWrite_le32 hw₂
    have hz₁ : (memBytesOf s₂ ma).size = (memBytesOf s₁ ma).size := by
      rw [he₁, size_wr _ hb₁]
    have hz₂ : (memBytesOf s' ma).size = (memBytesOf s₂ ma).size := by
      rw [he₂, size_wr _ hb₂]
    have hN : (memBytesOf s₁ ma).size = N := hb.size hi₁
    have hs' : SameOutside (memBytesOf s₁ ma) (memBytesOf s' ma) p 8 := by
      have a₁ : SameOutside (memBytesOf s₁ ma) (memBytesOf s₂ ma) p 8 := by
        rw [he₁]; exact sameOutside_wr _ hb₁ (Nat.le_refl _) (by omega)
      have a₂ : SameOutside (memBytesOf s₂ ma) (memBytesOf s' ma) p 8 := by
        rw [he₂]; exact sameOutside_wr _ hb₂ (by omega) (by omega)
      exact a₁.trans a₂
    have hlen : vs.length < 2 ^ 32 := by
      have := length_le_mul t vs.length
      have := hb.small
      omega
    have ew4 : wd (memBytesOf s' ma) (p + 4) = BitVec.ofNat 32 vs.length := by
      rw [he₂]; exact wd_wr_same _ hb₂
    have ew0 : wd (memBytesOf s' ma) p = BitVec.ofNat 32 q := by
      rw [he₂, wd_wr_ne _ hb₂ (Or.inr (Nat.le_refl _)), he₁]
      exact wd_wr_same _ hb₁
    refine ⟨t₁, hb.write (hb.write hi₁ hw₁) hw₂, h01,
      ⟨by rw [hs'.1, hso.1], fun i h₁ h₂ => (hs'.2 i h₁).trans (hso.2 i h₂)⟩, ?_⟩
    simp only [Holds]
    rw [ew4, ew0, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen,
      Nat.mod_eq_of_lt hq32, hz₂, hz₁]
    refine ⟨by omega, rfl, h0q, hq1, hqB, ?_⟩
    exact holdsL_frame (by rw [hz₂, hz₁]) (fun i h₁ h₂ => hs'.2 i (by omega)) t vs q
      (fun i h₁ h₂ => hs'.2 i (by omega)) hL

theorem list_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {t : LTy} {vs : List LVal} {s : Store Nat} {q : Nat} {s' : Store Nat} {t₀ : Nat},
      LList P ra ma t vs s q s' → Inv s t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside (memBytesOf s ma) (memBytesOf s' ma) t₀ (t₁ - t₀) ∧
        t₀ ≤ q ∧ q + vs.length * t.size ≤ t₁ ∧
        q + vs.length * t.size ≤ (memBytesOf s' ma).size ∧ q < 2 ^ 32 ∧
        HoldsL (memBytesOf s' ma) t₀ t₁ t vs q
  | t, vs, s, q, s', t₀, .mk (s₁ := s₁) hr _ hbd he, hi => by
    obtain ⟨t', hi', hmem, h0q, hqt⟩ := hb.realloc hi hr
    have hq32 : q < 2 ^ 32 := by obtain ⟨_, _, h⟩ := hr; exact h
    have hN : memLen s₁ ma = N := (memLen_eq s₁ ma).trans (hb.size hi')
    have hqt' := hqt (hN ▸ hbd)
    obtain ⟨t₁, hi₁, h't, hso, hL⟩ := elems_holds hb he hi' hqt'
    have hs' : (memBytesOf s' ma).size = N := hb.size hi₁
    have hs : (memBytesOf s ma).size = N := hb.size hi
    refine ⟨t₁, hi₁, by omega, ⟨by rw [hs', hs], fun i h => ?_⟩, h0q, by omega, by omega, hq32,
      holdsL_mono (by omega) (Nat.le_refl _) t vs q hL⟩
    rw [← hmem]
    exact hso.2 i (by omega) (by omega)

theorem elems_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {t : LTy} {vs : List LVal} {p : Nat} {s s' : Store Nat} {t₀ : Nat},
      LElems P ra ma t vs p s s' → Inv s t₀ → p + vs.length * t.size ≤ t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside2 (memBytesOf s ma) (memBytesOf s' ma) p (vs.length * t.size) t₀ (t₁ - t₀) ∧
        HoldsL (memBytesOf s' ma) t₀ t₁ t vs p
  | _, _, _, _, _, t₀, .nil, hi, _ =>
    ⟨t₀, hi, Nat.le_refl _, SameOutside2.refl _ _ _ _ _, trivial⟩
  | t, _, p, s, s', t₀, .cons (v := v) (vs := vs) (s₁ := s₁) hs he, hi, hp => by
    simp only [List.length_cons, Nat.succ_mul] at hp ⊢
    obtain ⟨t₁, hi₁, h01, hso₁, hH⟩ := store_holds hb hs hi (by omega)
    obtain ⟨t₂, hi₂, h12, hso₂, hL⟩ := elems_holds hb he hi₁ (by omega)
    refine ⟨t₂, hi₂, by omega, ⟨hso₂.1.trans hso₁.1, fun i h₁ h₂ =>
      (hso₂.2 i (by omega) (by omega)).trans (hso₁.2 i (by omega) (by omega))⟩, ?_⟩
    simp only [HoldsL]
    refine ⟨holds_mono (Nat.le_refl _) h12 t v p
      (holds_frame hso₂.1 (fun i h₁ h₂ => hso₂.2 i (by omega) (by omega)) t v p
        (fun i h₁ h₂ => hso₂.2 i (by omega) (by omega)) hH),
      holdsL_mono h01 (Nat.le_refl _) t vs _ hL⟩
end

/-- **The lowered arguments are in memory.** -/
theorem params_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {ts : List LTy} {vs : List LVal} {s : Store Nat} {fl : List Core.Val} {s' : Store Nat}
      {t₀ : Nat}, LParams P ra ma ts vs s fl s' → Inv s t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside (memBytesOf s ma) (memBytesOf s' ma) t₀ (t₁ - t₀) ∧
        FlatHolds (memBytesOf s' ma) t₀ t₁ ts vs fl
  | _, _, _, _, _, t₀, .nil, hi => ⟨t₀, hi, Nat.le_refl _, SameOutside.refl _ _ _, rfl⟩
  | _, _, _, _, _, _, .s32 (ts := ts) (vs := vs) (x := x) (fl := fl) h, hi => by
    obtain ⟨t₁, hi₁, h01, hso, hF⟩ := params_holds hb h hi
    refine ⟨t₁, hi₁, h01, hso, ?_⟩
    simp only [FlatHolds]
    exact ⟨fl, rfl, hF⟩
  | _, _, s, _, s', t₀, .list (t := t) (ts := ts) (us := us) (vs := vs) (q := q) (s₁ := s₁)
      (fl := fl) hl hp, hi => by
    obtain ⟨t₁, hi₁, h01, hso₁, h0q, hq1, hqB, hq32, hL⟩ := list_holds hb hl hi
    obtain ⟨t₂, hi₂, h12, hso₂, hF⟩ := params_holds hb hp hi₁
    have hlen : us.length < 2 ^ 32 := by
      have := length_le_mul t us.length
      have := hb.small
      have := hb.size hi₁
      omega
    refine ⟨t₂, hi₂, by omega, ⟨hso₂.1.trans hso₁.1, fun i h => ?_⟩, ?_⟩
    · exact (hso₂.2 i (by omega)).trans (hso₁.2 i (by omega))
    · simp only [FlatHolds]
      exact ⟨q, fl, rfl, hq32, hlen, h0q, by omega, by rw [hso₂.1]; exact hqB,
        holdsL_mono (Nat.le_refl _) h12 t us q
          (holdsL_frame hso₂.1 (fun i h₁ h₂ => hso₂.2 i (by omega)) t us q
            (fun i h₁ h₂ => hso₂.2 i (by omega)) hL),
        flatHolds_mono h01 (Nat.le_refl _) ts vs fl hF⟩

end

/-! ## Reading `list<s32>` -/

theorem words_succ (B : ByteArray) (p n : Nat) : words B p (n + 1) = wd B p :: words B (p + 4) n := by
  rw [show n + 1 = 1 + n by omega, words_append]
  simp [words]

/-- **The elements of a `list<s32>` are the words of its block.** -/
theorem holdsL_words {B : ByteArray} {lo hi : Nat} :
    ∀ (xs : List (BitVec 32)) (q : Nat), HoldsL B lo hi .s32 (xs.map .s32) q →
      words B q xs.length = xs
  | [], _, _ => rfl
  | x :: xs, q, h => by
    simp only [List.map_cons, HoldsL, Holds, LTy.size] at h
    rw [List.length_cons, words_succ, h.1.2, holdsL_words xs (q + 4) h.2]

end Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump
