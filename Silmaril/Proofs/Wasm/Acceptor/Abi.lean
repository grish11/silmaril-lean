module

public import Silmaril.Wasm.Acceptor.Abi.Defs

@[expose] public section

/-!
# The acceptor kit: reading canonical-ABI arguments back (proofs)

The reader contracts of the scalars, lists, two-field tuples and records, their closure under
bijections and weaker bounds, the read-back of a top-level `list<t>` argument
(`holdsL_listAt`), and of two list arguments from `FlatHolds` (`flatHolds_read2`).

A Silmaril addition; it generalises the per-acceptor read-back lemmas of the SAT, LRAT and
Farkas components (`holdsL_nested`, `holdsL_system`, `holdsL_s64s`, …).
-/

namespace Silmaril.Proofs.Wasm.Acceptor

open Silmaril.Wasm.Acceptor
open Silmaril.Wasm.Component.Reference.ListLift (LTy LVal Holds HoldsL HoldsF FlatHolds wd64)
open Silmaril.Wasm.Logic.Words (wd words)

variable {α β : Type} {B : ByteArray} {lo hi : Nat}

theorem listAt_succ (sz : Nat) (rd : ByteArray → Nat → α) (B : ByteArray) (p n : Nat) :
    listAt sz rd B p (n + 1) = rd B p :: listAt sz rd B (p + sz) n := by
  unfold listAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show p + sz * (i + 1) = p + sz + sz * i by rw [Nat.mul_succ]; omega]

@[simp] theorem length_listAt (sz : Nat) (rd : ByteArray → Nat → α) (B : ByteArray) (p n : Nat) :
    (listAt sz rd B p n).length = n := by
  simp [listAt]

/-- **A lowered top-level `list<t>`**: its elements read back, each meeting the bounds. -/
theorem holdsL_listAt {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn : ByteArray → Nat → Prop} (h : Reads t enc rd inn) :
    ∀ (xs : List α) (q : Nat), HoldsL B lo hi t (xs.map enc) q →
      listAt t.size rd B q xs.length = xs ∧ ∀ i < xs.length, inn B (q + t.size * i)
  | [], _, _ => ⟨rfl, by simp⟩
  | a :: xs, q, hH => by
    have hH' : Holds B lo hi t (enc a) q ∧ HoldsL B lo hi t (xs.map enc) (q + t.size) := hH
    obtain ⟨h₁, h₂⟩ := h a q hH'.1
    obtain ⟨ih₁, ih₂⟩ := holdsL_listAt h xs _ hH'.2
    refine ⟨by rw [List.length_cons, listAt_succ, h₁, ih₁], fun i hi => ?_⟩
    cases i with
    | zero => simpa using h₂
    | succ i =>
      have := ih₂ i (by simp only [List.length_cons] at hi; omega)
      rw [show q + t.size * (i + 1) = q + t.size + t.size * i by rw [Nat.mul_succ]; omega]
      exact this

theorem reads_s32 : Reads .s32 LVal.s32 wd NoBounds := fun _ _ h => ⟨h.2, trivial⟩

theorem reads_u32 : Reads .u32 LVal.u32 wd NoBounds := fun _ _ h => ⟨h.2, trivial⟩

theorem reads_s64 : Reads .s64 LVal.s64 wd64 NoBounds := fun _ _ h => ⟨h.2, trivial⟩

/-- **A list**: the `(ptr, len)` pair at `p`, its block in bounds. -/
theorem Reads.list {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn : ByteArray → Nat → Prop} (h : Reads t enc rd inn) :
    Reads (.list t) (fun xs => .list (xs.map enc)) (pairAt t.size rd) (listIn t inn) := by
  intro B lo hi xs p hH
  simp only [Holds, List.length_map] at hH
  obtain ⟨-, hlen, -, -, hB, hL⟩ := hH
  obtain ⟨h₁, h₂⟩ := holdsL_listAt h xs _ hL
  refine ⟨by unfold pairAt; rw [hlen]; exact h₁, ?_, ?_⟩
  · unfold PairIn
    rw [hlen, Nat.mul_comm]
    exact hB
  · rw [hlen]
    exact h₂

/-- **A two-field tuple**, the fields at their canonical-ABI offsets. -/
theorem Reads.tuple2 {t₁ t₂ : LTy} {e₁ : α → LVal} {e₂ : β → LVal} {r₁ : ByteArray → Nat → α}
    {r₂ : ByteArray → Nat → β} {i₁ i₂ : ByteArray → Nat → Prop} (h₁ : Reads t₁ e₁ r₁ i₁)
    (h₂ : Reads t₂ e₂ r₂ i₂) :
    Reads (.tuple t₁ [t₂]) (enc2 e₁ e₂) (read2 t₁ t₂ r₁ r₂) (in2 t₁ t₂ i₁ i₂) := by
  intro B lo hi c p hH
  have hH' : Holds B lo hi t₁ (e₁ c.1) (p + fieldOff₁ t₁) ∧
      Holds B lo hi t₂ (e₂ c.2) (p + fieldOff₂ t₁ t₂) ∧ True := hH
  obtain ⟨a₁, b₁⟩ := h₁ c.1 _ hH'.1
  obtain ⟨a₂, b₂⟩ := h₂ c.2 _ hH'.2.1
  exact ⟨by rw [read2, a₁, a₂], b₁, b₂⟩

/-- **A two-field record**, the fields at their canonical-ABI offsets. -/
theorem Reads.record2 {t₁ t₂ : LTy} {e₁ : α → LVal} {e₂ : β → LVal} {r₁ : ByteArray → Nat → α}
    {r₂ : ByteArray → Nat → β} {i₁ i₂ : ByteArray → Nat → Prop} (name l l₂ : String)
    (h₁ : Reads t₁ e₁ r₁ i₁) (h₂ : Reads t₂ e₂ r₂ i₂) :
    Reads (.record name l t₁ [(l₂, t₂)]) (enc2 e₁ e₂) (read2 t₁ t₂ r₁ r₂) (in2 t₁ t₂ i₁ i₂) := by
  intro B lo hi c p hH
  have hH' : Holds B lo hi t₁ (e₁ c.1) (p + fieldOff₁ t₁) ∧
      Holds B lo hi t₂ (e₂ c.2) (p + fieldOff₂ t₁ t₂) ∧ True := hH
  obtain ⟨a₁, b₁⟩ := h₁ c.1 _ hH'.1
  obtain ⟨a₂, b₂⟩ := h₂ c.2 _ hH'.2.1
  exact ⟨by rw [read2, a₁, a₂], b₁, b₂⟩

/-- **A type in bijection with a read one** (`f ∘ g = id`): read, then map by `f`. -/
theorem Reads.map {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn : ByteArray → Nat → Prop} (h : Reads t enc rd inn) (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) : Reads t (fun b => enc (g b)) (fun B p => f (rd B p)) inn := by
  intro B lo hi b p hH
  obtain ⟨h₁, h₂⟩ := h (g b) p hH
  exact ⟨by show f (rd B p) = b; rw [h₁, hfg], h₂⟩

/-- **Weaker bounds.** -/
theorem Reads.mono {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn inn' : ByteArray → Nat → Prop} (h : Reads t enc rd inn)
    (hi : ∀ B p, inn B p → inn' B p) : Reads t enc rd inn' := by
  intro B lo hi' a p hH
  obtain ⟨h₁, h₂⟩ := h a p hH
  exact ⟨h₁, hi _ _ h₂⟩

/-- `list<s32>` elements of a `list<list<s32>>`. -/
theorem reads_words :
    Reads (.list .s32) Silmaril.Wasm.Component.Reference.ListLift.LVal.ofWords (pairAt 4 wd)
      (PairIn 4) :=
  Reads.mono (Reads.list reads_s32) fun _ _ h => h.1

/-- Typing of encoded lists: each element's value has the element type. -/
theorem checkList_map {t : LTy} {f : α → LVal} (h : ∀ a, t.check (f a) = true) :
    ∀ l : List α, LTy.checkList t (l.map f) = true
  | [] => rfl
  | a :: l => by simp [LTy.checkList, h a, checkList_map h l]

/-! ## Two list arguments -/

/-- **Two lowered list arguments**: the flat arguments, the bounds and the holding blocks. -/
theorem flatHolds_two {t₁ t₂ : LTy} {us vs : List LVal}
    {fl : List Silmaril.Wasm.Execution.Core.Val}
    (h : FlatHolds B lo hi [.list t₁, .list t₂] [.list us, .list vs] fl) :
    ∃ q₁ q₂, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 us.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 vs.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ vs.length < 2 ^ 32 ∧
      q₁ + us.length * t₁.size ≤ B.size ∧ HoldsL B lo hi t₁ us q₁ ∧
      q₂ + vs.length * t₂.size ≤ B.size ∧ HoldsL B lo hi t₂ vs q₂ := by
  simp only [FlatHolds] at h
  obtain ⟨q₁, fl₁, rfl, hq₁, hl₁, -, -, hb₁, hL₁, q₂, fl₂, rfl, hq₂, hl₂, -, -, hb₂, hL₂, rfl⟩ := h
  exact ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hb₁, hL₁, hb₂, hL₂⟩

/-- **Two lowered list arguments, read back.** -/
theorem flatHolds_read2 {t₁ t₂ : LTy} {e₁ : α → LVal} {e₂ : β → LVal} {r₁ : ByteArray → Nat → α}
    {r₂ : ByteArray → Nat → β} {i₁ i₂ : ByteArray → Nat → Prop} (h₁ : Reads t₁ e₁ r₁ i₁)
    (h₂ : Reads t₂ e₂ r₂ i₂) {xs : List α} {ys : List β}
    {fl : List Silmaril.Wasm.Execution.Core.Val}
    (h : FlatHolds B lo hi [.list t₁, .list t₂] [.list (xs.map e₁), .list (ys.map e₂)] fl) :
    ∃ q₁ q₂, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 xs.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 ys.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ xs.length < 2 ^ 32 ∧ ys.length < 2 ^ 32 ∧
      ListIn t₁.size i₁ B q₁ xs.length ∧ listAt t₁.size r₁ B q₁ xs.length = xs ∧
      ListIn t₂.size i₂ B q₂ ys.length ∧ listAt t₂.size r₂ B q₂ ys.length = ys := by
  obtain ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, hb₁, hL₁, hb₂, hL₂⟩ := flatHolds_two h
  simp only [List.length_map] at hl₁ hl₂ hb₁ hb₂ ⊢
  obtain ⟨a₁, c₁⟩ := holdsL_listAt h₁ xs q₁ hL₁
  obtain ⟨a₂, c₂⟩ := holdsL_listAt h₂ ys q₂ hL₂
  exact ⟨q₁, q₂, rfl, hq₁, hq₂, hl₁, hl₂, ⟨by rw [Nat.mul_comm]; exact hb₁, c₁⟩, a₁,
    ⟨by rw [Nat.mul_comm]; exact hb₂, c₂⟩, a₂⟩

end Silmaril.Proofs.Wasm.Acceptor
