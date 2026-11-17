module

public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

/-!
# Lowered lists in the memory of a bump allocator: proofs

`params_holds`: `LParams` from a store with heap pointer `t₀` ends in a store with heap pointer
`t₁ ≥ t₀`, the memory unchanged outside `[t₀, t₁)` and holding the arguments (`FlatHolds`). By
mutual recursion on the lowering derivations (`store_holds`, `list_holds`, `elems_holds`,
`fields_holds`):

* an `s32` or `u32` is one 4-byte write at `p`, an `s64` one 8-byte write;
* a list allocates a block at or above the heap pointer (`BumpAlloc.realloc`), stores its
  elements there (they lie below the new heap pointer, their own blocks above it), then writes
  its `(ptr, len)` pair at `p`, which lies below the old heap pointer;
* a tuple or record stores its fields at their aligned offsets inside its own slot: the slot
  starts at a multiple of the record's alignment (the allocator's blocks are aligned, element
  sizes are multiples of the alignment, fields are placed at aligned offsets), so the absolute
  placement of `store_record` (`ABI.alignTo` of the address) is the relative one (`alignTo_add`)
  and stays inside the slot (`recordEnd_le`);
* each step changes only its slot and the bytes between the old and the new heap pointer
  (`SameOutside2`), and what an earlier step established depends only on bytes it owns
  (`holds_frame`, `holdsL_frame`, `holdsF_frame`), so it survives (`Agree`).

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

namespace ABI'
open Silmaril.Wasm.Component.ABI

/-! ## Alignment arithmetic -/

theorem le_alignTo (n : Nat) (a : Alignment) : n ≤ alignTo n a := by
  cases a <;> simp only [alignTo, Alignment.bytes] <;> omega

theorem alignTo_mod (n : Nat) (a : Alignment) : alignTo n a % a.bytes = 0 := by
  unfold alignTo
  exact Nat.mul_mod_left _ _

/-- Rounding up past a multiple of the alignment. -/
theorem alignTo_add {p : Nat} {a : Alignment} (hp : p % a.bytes = 0) (c : Nat) :
    alignTo (p + c) a = p + alignTo c a := by
  obtain ⟨k, rfl⟩ : ∃ k, p = a.bytes * k :=
    ⟨p / a.bytes, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp)).symm⟩
  cases a <;> simp only [alignTo, Alignment.bytes] <;> omega

theorem recordEnd_ge (c : Nat) (ls : List Layout) : c ≤ recordEnd c ls := by
  induction ls generalizing c with
  | nil => exact Nat.le_refl _
  | cons l ls ih =>
    exact Nat.le_trans (Nat.le_trans (le_alignTo c l.alignment) (Nat.le_add_right _ _)) (ih _)

theorem recordEnd_le (ls : List Layout) : recordEnd 0 ls ≤ (recordLayout ls).size := by
  unfold recordLayout
  rw [Layout.size_rounded]
  exact le_alignTo _ _

theorem join_mod_left (a b : Alignment) : (a.join b).bytes % a.bytes = 0 := by
  cases a <;> cases b <;> decide

theorem join_mod_right (a b : Alignment) : (a.join b).bytes % b.bytes = 0 := by
  cases a <;> cases b <;> decide

theorem mod_trans {p a b : Nat} (h₁ : p % a = 0) (h₂ : a % b = 0) : p % b = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h₂) (Nat.dvd_of_mod_eq_zero h₁))

/-- A record's alignment is a multiple of every field's. -/
theorem recordAlignment_mod : ∀ (ls : List Layout), ∀ l ∈ ls,
    (recordAlignment ls).bytes % l.alignment.bytes = 0
  | [], _, h => nomatch h
  | l :: ls, l', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact join_mod_left _ _
    · exact mod_trans (join_mod_right _ _) (recordAlignment_mod ls l' h)

theorem size_mod (l : Layout) (p : Nat) (h : p % l.alignment.bytes = 0) :
    (p + l.size) % l.alignment.bytes = 0 := by
  unfold Layout.size
  rw [Nat.add_mul_mod_self_right]
  exact h

end ABI'

open ABI'

/-! ## Layouts of the fragment's types -/

theorem layoutFields_eq : ∀ fs : List (String × LTy),
    LTy.layoutFields fs = LTy.layoutList (fs.map (·.2))
  | [] => rfl
  | (_, t) :: fs => by
    simp only [LTy.layoutFields, LTy.layoutList, List.map_cons, layoutFields_eq fs]

theorem mem_layoutList {t : LTy} : ∀ {ts : List LTy}, t ∈ ts → t.layout ∈ LTy.layoutList ts
  | [], h => nomatch h
  | u :: ts, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_layoutList h)

theorem layout_tuple (t : LTy) (ts : List LTy) :
    (LTy.tuple t ts).layout = Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList (t :: ts)) :=
  rfl

theorem layout_record (n l : String) (t : LTy) (fs : List (String × LTy)) :
    (LTy.record n l t fs).layout =
      Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList (t :: fs.map (·.2))) := by
  simp only [LTy.layout, LTy.layoutList, layoutFields_eq]

/-- A multiple of a record's alignment is a multiple of every field's. -/
theorem fields_aligned {ts : List LTy} {p : Nat}
    (h : p % (Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList ts)).alignment.bytes = 0) :
    ∀ t ∈ ts, p % t.align.bytes = 0 := fun _ ht =>
  mod_trans h (recordAlignment_mod _ _ (mem_layoutList ht))

theorem size_head_le (l : Silmaril.Wasm.Component.ABI.Layout)
    (ls : List Silmaril.Wasm.Component.ABI.Layout) :
    l.size ≤ (Silmaril.Wasm.Component.ABI.recordLayout (l :: ls)).size := by
  have h₁ := recordEnd_le (l :: ls)
  have h₂ := recordEnd_ge (Silmaril.Wasm.Component.ABI.alignTo 0 l.alignment + l.size) ls
  show l.size ≤ _
  simp only [Silmaril.Wasm.Component.ABI.recordEnd, Silmaril.Wasm.Component.ABI.placeField]
    at h₁
  omega

theorem four_le_size : ∀ t : LTy, 4 ≤ t.size
  | .s32 | .u32 => by decide
  | .list t => by rw [LTy.size_list]; decide
  | .s64 => by decide
  | .tuple t ts => Nat.le_trans (four_le_size t) (size_head_le t.layout _)
  | .record _ _ t fs => Nat.le_trans (four_le_size t) (size_head_le t.layout _)

theorem length_le_mul (t : LTy) (n : Nat) : n ≤ n * t.size :=
  Nat.le_mul_of_pos_right n (by have := four_le_size t; omega)

/-! ## Bytes -/

/-- `B'` has the bytes of `B` on `[a, b)`. -/
def Agree (B B' : ByteArray) (a b : Nat) : Prop :=
  ∀ i, a ≤ i → i < b → B'.data.toList[i]? = B.data.toList[i]?

theorem load_agree {B B' : ByteArray} {a n : Nat} (hs : B'.size = B.size)
    (h : Agree B B' a (a + n)) : Memory.load B' a n = Memory.load B a n := by
  by_cases hB : a + n ≤ B.size
  · have hB' : a + n ≤ B'.size := hs ▸ hB
    have hr : Silmaril.Wasm.Logic.Core.bytesAt B' ⟨a, n⟩ =
        Silmaril.Wasm.Logic.Core.bytesAt B ⟨a, n⟩ := by
      apply List.ext_getElem?
      intro i
      rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt, Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
      dsimp only
      split
      · exact h _ (by omega) (by omega)
      · rfl
    rw [Silmaril.Wasm.Logic.Core.load_eq hB, Silmaril.Wasm.Logic.Core.load_eq hB', hr]
  · rw [Silmaril.Wasm.Logic.Core.load_eq_none (B := B) (a := a) (n := n) (by omega),
      Silmaril.Wasm.Logic.Core.load_eq_none (B := B') (a := a) (n := n) (by rw [hs]; omega)]

theorem wd_agree {B B' : ByteArray} {a : Nat} (hs : B'.size = B.size)
    (h : Agree B B' a (a + 4)) : wd B' a = wd B a := by
  rw [wd, wd, load_agree hs h]

theorem wd64_agree {B B' : ByteArray} {a : Nat} (hs : B'.size = B.size)
    (h : Agree B B' a (a + 8)) : wd64 B' a = wd64 B a := by
  rw [wd64, wd64, load_agree hs h]

theorem memLen_eq (s : Store Nat) (ma : Nat) : memLen s ma = (memBytesOf s ma).size := by
  unfold memLen memBytesOf
  cases s.mems[ma]? <;> rfl

/-- A write through `memWrite?` writes the bytes of memory `ma`. -/
theorem memWrite_bytes {s s' : Store Nat} {ma p : Nat} {D : ByteArray}
    (h : Silmaril.Wasm.SingleThreaded.memWrite? s ma p D = some s') :
    Memory.writeBytes (memBytesOf s ma) p D = some (memBytesOf s' ma) := by
  obtain ⟨mi, b, hm, hw, rfl⟩ := Silmaril.Wasm.Component.Engine.Core3.memWrite?_eq_some h
  have hm' : memBytesOf s ma = mi.bytes := by simp [memBytesOf, hm]
  have hlt : ma < s.mems.length := (List.getElem?_eq_some_iff.mp hm).1
  have hb : memBytesOf (s.setMem ma { mi with bytes := b }) ma = b := by
    simp [memBytesOf, Store.setMem, List.getElem?_set_self hlt]
  rw [hm', hb]
  exact hw

/-- A write changes nothing outside the written range. -/
theorem sameOutside_writeBytes {B B' D : ByteArray} {a p len : Nat}
    (hw : Memory.writeBytes B a D = some B') (hp : p ≤ a) (hl : a + D.size ≤ p + len) :
    SameOutside B B' p len := by
  obtain ⟨hb, hL⟩ := Silmaril.Wasm.Logic.Core.toList_writeBytes hw
  have hlen : a + D.data.toList.length ≤ B.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]
    exact hb
  refine ⟨Memory.writeBytes_size _ _ _ _ hw, fun i hi => ?_⟩
  rw [hL, show D.size = D.data.toList.length from rfl,
    Silmaril.Wasm.Logic.Core.getElem?_splice hlen]
  have hd : D.data.toList.length = D.size := by
    simp only [Array.length_toList, ByteArray.size_data]
  split
  · omega
  · rfl

/-- A write of a word through `memWrite?`. -/
theorem memWrite_le32 {s s' : Store Nat} {ma p : Nat} {x : BitVec 32}
    (h : Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le32 x) = some s') :
    p + 4 ≤ (memBytesOf s ma).size ∧ memBytesOf s' ma = wr (memBytesOf s ma) p x := by
  have hw := memWrite_bytes h
  have hb : p + 4 ≤ (memBytesOf s ma).size := by
    have := (Silmaril.Wasm.Logic.Core.toList_writeBytes hw).1
    simpa [le32] using this
  have hw' : Memory.writeBytes (memBytesOf s ma) p (le32 x) = some (wr (memBytesOf s ma) p x) :=
    store_wr x hb
  rw [hw'] at hw
  exact ⟨hb, (Option.some.inj hw).symm⟩

/-- A write of a 64-bit word through `memWrite?`. -/
theorem memWrite_le64 {s s' : Store Nat} {ma p : Nat} {x : BitVec 64}
    (h : Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le64 x) = some s') :
    p + 8 ≤ (memBytesOf s ma).size ∧
      SameOutside (memBytesOf s ma) (memBytesOf s' ma) p 8 ∧ wd64 (memBytesOf s' ma) p = x := by
  have hw := memWrite_bytes h
  have hsz : (le64 x).size = 8 := Memory.encodeLE_size 8 x.toNat
  have hb : p + 8 ≤ (memBytesOf s ma).size := by
    have := (Silmaril.Wasm.Logic.Core.toList_writeBytes hw).1
    rw [hsz] at this
    exact this
  refine ⟨hb, sameOutside_writeBytes hw (Nat.le_refl _) (by rw [hsz]), ?_⟩
  have hs : Memory.store (memBytesOf s ma) p (count := 8) x = some (memBytesOf s' ma) := hw
  simp only [wd64, Memory.load_store _ _ _ _ _ hs, Option.getD_some]

/-! ## Frames and widening of the readings -/

section
variable {B B' : ByteArray} {lo hi : Nat}

mutual
theorem holds_frame (hs : B'.size = B.size) (hag : Agree B B' lo hi) :
    ∀ (t : LTy) (v : LVal) (p : Nat), Agree B B' p (p + t.size) →
      Holds B lo hi t v p → Holds B' lo hi t v p
  | .s32, .s32 x, p, hp, h => by
    simp only [Holds] at h ⊢
    exact ⟨hs ▸ h.1, (wd_agree hs fun i h₁ h₂ => hp i h₁ (by simp only [LTy.size_s32]; omega)).trans h.2⟩
  | .u32, .u32 x, p, hp, h => by
    simp only [Holds] at h ⊢
    exact ⟨hs ▸ h.1, (wd_agree hs fun i h₁ h₂ => hp i h₁ (by
      change i < p + 4; omega)).trans h.2⟩
  | .s64, .s64 x, p, hp, h => by
    simp only [Holds] at h ⊢
    exact ⟨hs ▸ h.1, (wd64_agree hs fun i h₁ h₂ => hp i h₁ (by
      change i < p + 8; omega)).trans h.2⟩
  | .list t, .list vs, p, hp, h => by
    simp only [Holds] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have e0 : wd B' p = wd B p :=
      wd_agree hs fun i h₁ h₂ => hp i h₁ (by simp only [LTy.size_list]; omega)
    have e4 : wd B' (p + 4) = wd B (p + 4) :=
      wd_agree hs fun i h₁ h₂ => hp i (by omega) (by simp only [LTy.size_list]; omega)
    rw [e0, e4, hs]
    exact ⟨h1, h2, h3, h4, h5,
      holdsL_frame hs hag t vs _ (fun i h₁ h₂ => hag i (by omega) (by omega)) h6⟩
  | .tuple t ts, .fields vs, p, hp, h => by
    simp only [Holds] at h ⊢
    have hz : (LTy.tuple t ts).size =
        (Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList (t :: ts))).size := rfl
    have hr := recordEnd_le (LTy.layoutList (t :: ts))
    exact holdsF_frame hs hag (t :: ts) vs p 0 (fun i h₁ h₂ => hp i (by omega) (by omega)) h
  | .record nm l t fs, .fields vs, p, hp, h => by
    simp only [Holds] at h ⊢
    have hz : (LTy.record nm l t fs).size =
        (Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList (t :: fs.map (·.2)))).size := by
      unfold LTy.size
      rw [layout_record]
    have hr := recordEnd_le (LTy.layoutList (t :: fs.map (·.2)))
    exact holdsF_frame hs hag (t :: fs.map (·.2)) vs p 0
      (fun i h₁ h₂ => hp i (by omega) (by omega)) h
  | .s32, .list _, _, _, h | .s32, .u32 _, _, _, h | .s32, .s64 _, _, _, h
  | .s32, .fields _, _, _, h | .list _, .s32 _, _, _, h | .list _, .u32 _, _, _, h
  | .list _, .s64 _, _, _, h | .list _, .fields _, _, _, h | .u32, .s32 _, _, _, h
  | .u32, .list _, _, _, h | .u32, .s64 _, _, _, h | .u32, .fields _, _, _, h
  | .s64, .s32 _, _, _, h | .s64, .list _, _, _, h | .s64, .u32 _, _, _, h
  | .s64, .fields _, _, _, h | .tuple _ _, .s32 _, _, _, h | .tuple _ _, .list _, _, _, h
  | .tuple _ _, .u32 _, _, _, h | .tuple _ _, .s64 _, _, _, h
  | .record _ _ _ _, .s32 _, _, _, h | .record _ _ _ _, .list _, _, _, h
  | .record _ _ _ _, .u32 _, _, _, h | .record _ _ _ _, .s64 _, _, _, h => by
    simp [Holds] at h

theorem holdsL_frame (hs : B'.size = B.size) (hag : Agree B B' lo hi) :
    ∀ (t : LTy) (vs : List LVal) (q : Nat), Agree B B' q (q + vs.length * t.size) →
      HoldsL B lo hi t vs q → HoldsL B' lo hi t vs q
  | _, [], _, _, _ => trivial
  | t, v :: vs, q, hq, h => by
    simp only [HoldsL] at h ⊢
    simp only [List.length_cons, Nat.succ_mul] at hq
    exact ⟨holds_frame hs hag t v q (fun i h₁ h₂ => hq i h₁ (by omega)) h.1,
      holdsL_frame hs hag t vs _ (fun i h₁ h₂ => hq i (by omega) (by omega)) h.2⟩

theorem holdsF_frame (hs : B'.size = B.size) (hag : Agree B B' lo hi) :
    ∀ (ts : List LTy) (vs : List LVal) (p c : Nat),
      Agree B B' (p + c) (p + Silmaril.Wasm.Component.ABI.recordEnd c (LTy.layoutList ts)) →
      HoldsF B lo hi ts vs p c → HoldsF B' lo hi ts vs p c
  | [], [], _, _, _, _ => trivial
  | t :: ts, v :: vs, p, c, hq, h => by
    simp only [HoldsF] at h ⊢
    have h₁ := le_alignTo c t.align
    have h₂ := recordEnd_ge (Silmaril.Wasm.Component.ABI.alignTo c t.align + t.size)
      (LTy.layoutList ts)
    have e : Silmaril.Wasm.Component.ABI.recordEnd c (LTy.layoutList (t :: ts)) =
        Silmaril.Wasm.Component.ABI.recordEnd
          (Silmaril.Wasm.Component.ABI.alignTo c t.align + t.size) (LTy.layoutList ts) := rfl
    rw [e] at hq
    exact ⟨holds_frame hs hag t v _ (fun i h₃ h₄ => hq i (by omega) (by omega)) h.1,
      holdsF_frame hs hag ts vs p _ (fun i h₃ h₄ => hq i (by omega) (by omega)) h.2⟩
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp [HoldsF] at h
end

end

section
variable {B : ByteArray} {lo hi lo' hi' : Nat}

mutual
theorem holds_mono (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ (t : LTy) (v : LVal) (p : Nat), Holds B lo hi t v p → Holds B lo' hi' t v p
  | .s32, .s32 _, _, h => h
  | .u32, .u32 _, _, h => h
  | .s64, .s64 _, _, h => h
  | .list t, .list vs, p, h => by
    simp only [Holds] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, by omega, by omega, h5, holdsL_mono hl hh t vs _ h6⟩
  | .tuple t ts, .fields vs, p, h => by
    simp only [Holds] at h ⊢
    exact holdsF_mono hl hh _ vs p 0 h
  | .record _ _ t fs, .fields vs, p, h => by
    simp only [Holds] at h ⊢
    exact holdsF_mono hl hh _ vs p 0 h
  | .s32, .list _, _, h | .s32, .u32 _, _, h | .s32, .s64 _, _, h | .s32, .fields _, _, h
  | .list _, .s32 _, _, h | .list _, .u32 _, _, h | .list _, .s64 _, _, h
  | .list _, .fields _, _, h | .u32, .s32 _, _, h | .u32, .list _, _, h | .u32, .s64 _, _, h
  | .u32, .fields _, _, h | .s64, .s32 _, _, h | .s64, .list _, _, h | .s64, .u32 _, _, h
  | .s64, .fields _, _, h | .tuple _ _, .s32 _, _, h | .tuple _ _, .list _, _, h
  | .tuple _ _, .u32 _, _, h | .tuple _ _, .s64 _, _, h | .record _ _ _ _, .s32 _, _, h
  | .record _ _ _ _, .list _, _, h | .record _ _ _ _, .u32 _, _, h
  | .record _ _ _ _, .s64 _, _, h => by simp [Holds] at h

theorem holdsL_mono (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ (t : LTy) (vs : List LVal) (q : Nat), HoldsL B lo hi t vs q → HoldsL B lo' hi' t vs q
  | _, [], _, _ => trivial
  | t, v :: vs, q, h => by
    simp only [HoldsL] at h ⊢
    exact ⟨holds_mono hl hh t v q h.1, holdsL_mono hl hh t vs _ h.2⟩

theorem holdsF_mono (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    ∀ (ts : List LTy) (vs : List LVal) (p c : Nat), HoldsF B lo hi ts vs p c →
      HoldsF B lo' hi' ts vs p c
  | [], [], _, _, _ => trivial
  | t :: ts, v :: vs, p, c, h => by
    simp only [HoldsF] at h ⊢
    exact ⟨holds_mono hl hh t v _ h.1, holdsF_mono hl hh ts vs p _ h.2⟩
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [HoldsF] at h
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
  | .s32 :: _, .list _ :: _, _, h | .s32 :: _, .u32 _ :: _, _, h
  | .s32 :: _, .s64 _ :: _, _, h | .s32 :: _, .fields _ :: _, _, h
  | .list _ :: _, .s32 _ :: _, _, h | .list _ :: _, .u32 _ :: _, _, h
  | .list _ :: _, .s64 _ :: _, _, h | .list _ :: _, .fields _ :: _, _, h
  | .u32 :: _, _ :: _, _, h | .s64 :: _, _ :: _, _, h | .tuple _ _ :: _, _ :: _, _, h
  | .record _ _ _ _ :: _, _ :: _, _, h => by simp [FlatHolds] at h

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
  | .s32 :: _, .list _ :: _, _, h | .s32 :: _, .u32 _ :: _, _, h
  | .s32 :: _, .s64 _ :: _, _, h | .s32 :: _, .fields _ :: _, _, h
  | .list _ :: _, .s32 _ :: _, _, h | .list _ :: _, .u32 _ :: _, _, h
  | .list _ :: _, .s64 _ :: _, _, h | .list _ :: _, .fields _ :: _, _, h
  | .u32 :: _, _ :: _, _, h | .s64 :: _, _ :: _, _, h | .tuple _ _ :: _, _ :: _, _, h
  | .record _ _ _ _ :: _, _ :: _, _, h => by simp [FlatHolds] at h

/-! ## The lowering -/

section
variable {P : Profile} {ra ma N : Nat} {Inv : Store Nat → Nat → Prop}

/-- A 4-byte write at `p` below the heap pointer. -/
theorem word_holds (hb : BumpAlloc P ra ma N Inv) {x : BitVec 32} {p : Nat} {s s' : Store Nat}
    {t₀ : Nat} (hw : Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le32 x) = some s')
    (hi : Inv s t₀) :
    Inv s' t₀ ∧ SameOutside2 (memBytesOf s ma) (memBytesOf s' ma) p 4 t₀ (t₀ - t₀) ∧
      p + 4 ≤ (memBytesOf s' ma).size ∧ wd (memBytesOf s' ma) p = x := by
  obtain ⟨hb4, he⟩ := memWrite_le32 hw
  refine ⟨hb.write hi hw, ?_, ?_⟩
  · rw [he]
    exact (sameOutside_wr x hb4 (Nat.le_refl _) (Nat.le_refl _)).two _ _
  · rw [he]
    exact ⟨by rw [size_wr x hb4]; exact hb4, wd_wr_same x hb4⟩

mutual
theorem store_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {t : LTy} {v : LVal} {p : Nat} {s s' : Store Nat} {t₀ : Nat},
      LStore P ra ma t v p s s' → Inv s t₀ → p % t.align.bytes = 0 → p + t.size ≤ t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside2 (memBytesOf s ma) (memBytesOf s' ma) p t.size t₀ (t₁ - t₀) ∧
        Holds (memBytesOf s' ma) t₀ t₁ t v p
  | _, _, _, _, _, t₀, .s32 hw, hi, _, _ => by
    obtain ⟨hi', hso, hB, hx⟩ := word_holds hb hw hi
    exact ⟨t₀, hi', Nat.le_refl _, hso, hB, hx⟩
  | _, _, _, _, _, t₀, .u32 hw, hi, _, _ => by
    obtain ⟨hi', hso, hB, hx⟩ := word_holds hb hw hi
    exact ⟨t₀, hi', Nat.le_refl _, hso, hB, hx⟩
  | _, _, p, s, s', t₀, .s64 (x := x) hw, hi, _, _ => by
    obtain ⟨hb8, hso, hx⟩ := memWrite_le64 hw
    refine ⟨t₀, hb.write hi hw, Nat.le_refl _, hso.two _ _, ?_⟩
    simp only [Holds]
    exact ⟨by rw [hso.1]; exact hb8, hx⟩
  | _, _, p, s, s', t₀, .tuple (t := t) (ts := ts) (vs := vs) hf, hi, hal, hp => by
    have hz : (LTy.tuple t ts).size =
        (Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList (t :: ts))).size := rfl
    have hr := recordEnd_le (LTy.layoutList (t :: ts))
    obtain ⟨t₁, hi₁, h01, hso, hF⟩ := fields_holds hb hf (Nat.add_zero p).symm hi
      (fields_aligned hal) (by omega)
    refine ⟨t₁, hi₁, h01, hso.mono (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _), ?_⟩
    simp only [Holds]
    exact hF
  | _, _, p, s, s', t₀, .record (name := nm) (l := l) (t := t) (fs := fs) (vs := vs) hf, hi, hal,
      hp => by
    have hz : (LTy.record nm l t fs).size =
        (Silmaril.Wasm.Component.ABI.recordLayout (LTy.layoutList (t :: fs.map (·.2)))).size := by
      unfold LTy.size
      rw [layout_record]
    have ha : (LTy.record nm l t fs).align =
        (Silmaril.Wasm.Component.ABI.recordLayout
          (LTy.layoutList (t :: fs.map (·.2)))).alignment := by
      unfold LTy.align
      rw [layout_record]
    have hr := recordEnd_le (LTy.layoutList (t :: fs.map (·.2)))
    rw [ha] at hal
    obtain ⟨t₁, hi₁, h01, hso, hF⟩ := fields_holds hb hf (Nat.add_zero p).symm hi
      (fields_aligned hal) (by omega)
    refine ⟨t₁, hi₁, h01, hso.mono (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _), ?_⟩
    simp only [Holds]
    exact hF
  | _, _, p, s, s', t₀, .list (t := t) (vs := vs) (s₁ := s₁) (s₂ := s₂) (q := q) hl hw₁ hw₂,
      hi, _, hp => by
    simp only [LTy.size_list] at hp ⊢
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
  | t, vs, s, q, s', t₀, .mk (s₁ := s₁) hr hal hbd he, hi => by
    obtain ⟨t', hi', hmem, h0q, hqt⟩ := hb.realloc hi hr
    have hq32 : q < 2 ^ 32 := by obtain ⟨_, _, h⟩ := hr; exact h
    have hN : memLen s₁ ma = N := (memLen_eq s₁ ma).trans (hb.size hi')
    have hqt' := hqt (hN ▸ hbd)
    obtain ⟨t₁, hi₁, h't, hso, hL⟩ := elems_holds hb he hi' hal hqt'
    have hs' : (memBytesOf s' ma).size = N := hb.size hi₁
    have hs : (memBytesOf s ma).size = N := hb.size hi
    refine ⟨t₁, hi₁, by omega, ⟨by rw [hs', hs], fun i h => ?_⟩, h0q, by omega, by omega, hq32,
      holdsL_mono (by omega) (Nat.le_refl _) t vs q hL⟩
    rw [← hmem]
    exact hso.2 i (by omega) (by omega)

theorem elems_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {t : LTy} {vs : List LVal} {p : Nat} {s s' : Store Nat} {t₀ : Nat},
      LElems P ra ma t vs p s s' → Inv s t₀ → p % t.align.bytes = 0 →
      p + vs.length * t.size ≤ t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside2 (memBytesOf s ma) (memBytesOf s' ma) p (vs.length * t.size) t₀ (t₁ - t₀) ∧
        HoldsL (memBytesOf s' ma) t₀ t₁ t vs p
  | _, _, _, _, _, t₀, .nil, hi, _, _ =>
    ⟨t₀, hi, Nat.le_refl _, SameOutside2.refl _ _ _ _ _, trivial⟩
  | t, _, p, s, s', t₀, .cons (v := v) (vs := vs) (s₁ := s₁) hs he, hi, hal, hp => by
    simp only [List.length_cons, Nat.succ_mul] at hp ⊢
    obtain ⟨t₁, hi₁, h01, hso₁, hH⟩ := store_holds hb hs hi hal (by omega)
    obtain ⟨t₂, hi₂, h12, hso₂, hL⟩ := elems_holds hb he hi₁ (size_mod t.layout p hal) (by omega)
    refine ⟨t₂, hi₂, by omega, ⟨hso₂.1.trans hso₁.1, fun i h₁ h₂ =>
      (hso₂.2 i (by omega) (by omega)).trans (hso₁.2 i (by omega) (by omega))⟩, ?_⟩
    simp only [HoldsL]
    refine ⟨holds_mono (Nat.le_refl _) h12 t v p
      (holds_frame hso₂.1 (fun i h₁ h₂ => hso₂.2 i (by omega) (by omega)) t v p
        (fun i h₁ h₂ => hso₂.2 i (by omega) (by omega)) hH),
      holdsL_mono h01 (Nat.le_refl _) t vs _ hL⟩

theorem fields_holds (hb : BumpAlloc P ra ma N Inv) :
    ∀ {ts : List LTy} {vs : List LVal} {q p c : Nat} {s s' : Store Nat} {t₀ : Nat},
      LFields P ra ma ts vs q s s' → q = p + c → Inv s t₀ → (∀ t ∈ ts, p % t.align.bytes = 0) →
      p + Silmaril.Wasm.Component.ABI.recordEnd c (LTy.layoutList ts) ≤ t₀ →
      ∃ t₁, Inv s' t₁ ∧ t₀ ≤ t₁ ∧
        SameOutside2 (memBytesOf s ma) (memBytesOf s' ma) (p + c)
          (Silmaril.Wasm.Component.ABI.recordEnd c (LTy.layoutList ts) - c) t₀ (t₁ - t₀) ∧
        HoldsF (memBytesOf s' ma) t₀ t₁ ts vs p c
  | _, _, _, _, _, _, _, t₀, .nil, _, hi, _, _ =>
    ⟨t₀, hi, Nat.le_refl _, SameOutside2.refl _ _ _ _ _, trivial⟩
  | _, _, q, p, c, s, s', t₀, .cons (t := t) (ts := ts) (v := v) (vs := vs) (s₁ := s₁) hs hf,
      hq, hi, hA, hp => by
    subst hq
    have hpa : p % t.align.bytes = 0 := hA t List.mem_cons_self
    have ho := alignTo_add hpa c
    have hg := le_alignTo c t.align
    have e : Silmaril.Wasm.Component.ABI.recordEnd c (LTy.layoutList (t :: ts)) =
        Silmaril.Wasm.Component.ABI.recordEnd
          (Silmaril.Wasm.Component.ABI.alignTo c t.align + t.size) (LTy.layoutList ts) := rfl
    have hE := recordEnd_ge (Silmaril.Wasm.Component.ABI.alignTo c t.align + t.size)
      (LTy.layoutList ts)
    rw [e] at hp ⊢
    rw [ho] at hs hf
    obtain ⟨t₁, hi₁, h01, hso₁, hH⟩ := store_holds hb hs hi
      (by rw [Nat.add_mod, hpa, alignTo_mod, Nat.zero_add, Nat.zero_mod]) (by omega)
    obtain ⟨t₂, hi₂, h12, hso₂, hF⟩ := fields_holds hb hf (Nat.add_assoc _ _ _) hi₁
      (fun u hu => hA u (List.mem_cons_of_mem _ hu)) (by omega)
    refine ⟨t₂, hi₂, by omega, ⟨hso₂.1.trans hso₁.1, fun i h₁ h₂ =>
      (hso₂.2 i (by omega) (by omega)).trans (hso₁.2 i (by omega) (by omega))⟩, ?_⟩
    simp only [HoldsF]
    refine ⟨holds_mono (Nat.le_refl _) h12 t v _
      (holds_frame hso₂.1 (fun i h₁ h₂ => hso₂.2 i (by omega) (by omega)) t v _
        (fun i h₁ h₂ => hso₂.2 i (by omega) (by omega)) hH),
      holdsF_mono h01 (Nat.le_refl _) ts vs p _ hF⟩
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
    simp only [List.map_cons, HoldsL, Holds, LTy.size_s32] at h
    rw [List.length_cons, words_succ, h.1.2, holdsL_words xs (q + 4) h.2]

end Silmaril.Proofs.Wasm.Component.Reference.ListLift.Bump
