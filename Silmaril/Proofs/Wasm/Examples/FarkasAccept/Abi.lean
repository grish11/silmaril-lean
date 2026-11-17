module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Calls
public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Read

@[expose] public section

/-!
# The canonical-ABI memory and the heap pointer: rules

In the acceptor's fixture `accX top B₁` the checker's state is followed by one further memory,
the canonical-ABI memory holding the bytes `B₁` (memory `1` of the module instance), and one
further global, the heap pointer (global `4`). `InA top B₁ s` says the store has this layout;
`w_ld1` and `w_ld64` load an `i32` and an `i64` word of `B₁`, `w_gsetHeap` writes the heap
pointer (after which the acceptor's code no longer needs the layout), `w_drop` drops a value,
and `w_tail` is the end of the check: `top := heapBase`, answer local `8`, with the
postcondition `checkPost Goal` (a nonzero answer only if `Goal`). A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.Farkas
open Silmaril.Wasm.Examples.LRAT (fr vals_rev_cons vals_rev_push w_const w_lget w_end)
open Silmaril.Wasm.Examples.Common (bodyPost)
open Silmaril.Wasm.Examples.FarkasAccept (accS ld1 ld64 heapBase gHeap dw accG32 accMt)
open Silmaril.Wasm.Examples.LRAT (c32 lget gset)

/-- Normalise literal frames. -/
macro "fnorm" : tactic => `(tactic| try simp only [List.getD_cons_succ, List.getD_cons_zero,
  List.set_cons_succ, List.set_cons_zero])

variable {P : Profile} {host : HostSemantics Nat} {top : BitVec 32} {B₁ : ByteArray}
  {s : Store Nat} {L : List (BitVec 32)} {vs : List Val} {rest : List Admin} {Q : Post Nat}

/-- The store has the acceptor's layout (some checker state). -/
def InA (top : BitVec 32) (B₁ : ByteArray) (s : Store Nat) : Prop :=
  ∃ m, HoldsX (accX top B₁) accS.funcs s m

theorem RepA.inA {rs : Silmaril.Logic.LinArith.WRows} (h : RepA top B₁ rs s) : InA top B₁ s := by
  obtain ⟨m, hH, -⟩ := h
  exact ⟨m, hH⟩

theorem SizedA.inA (h : SizedA top B₁ s) : InA top B₁ s := by
  obtain ⟨m, hH, -⟩ := h
  exact ⟨m, hH⟩

theorem InA.mem1 (h : InA top B₁ s) : s.mem? (fr accMi L) ⟨1⟩ = some (1, ⟨accMt, B₁⟩) := by
  obtain ⟨m, s₀, -, rfl⟩ := h
  simp [Store.mem?, fr, Idx.toNat, acc_mi.2.1, withMachX, accX]

theorem InA.glob4 (h : InA top B₁ s) :
    s.global? (fr accMi L) ⟨⟨4 % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ =
      some (4, ⟨accG32, Val.i32 top⟩) := by
  obtain ⟨m, s₀, -, rfl⟩ := h
  simp [Store.global?, fr, Idx.toNat, acc_mi.1, withMachX, accX, Mach.globals]

/-- `i32.load` from the ABI memory, at a known address in bounds. -/
theorem w_ld1 (hA : InA top B₁ s) {a : BitVec 32} {n : Nat} (ha : a.toNat = n)
    (hb : n + 4 ≤ B₁.size)
    (h : HWP P host s (fr accMi L)
      (vals (Val.i32 (Silmaril.Wasm.Logic.Words.wd B₁ n) :: vs).reverse ++ rest) Q) :
    HWP P host s (fr accMi L) (vals (Val.i32 a :: vs).reverse ++ .plain ld1 :: rest) Q := by
  subst ha
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  have hl : Memory.load B₁ (effAddr a.toNat ⟨2, 0⟩) (IntType.i32.width / 8) =
      some (Silmaril.Wasm.Logic.Words.wd B₁ a.toNat) :=
    Silmaril.Wasm.Examples.LRAT.load_wd (B := B₁) (by simp only [effAddr]; exact hb)
  exact Wp.intLoad (m := .part) (a := .i32) (i := a) hA.mem1 hl h

/-- `i64.load` from the ABI memory, at a known address in bounds. -/
theorem w_ld64 (hA : InA top B₁ s) {a : BitVec 32} {n : Nat} (ha : a.toNat = n)
    (hb : n + 8 ≤ B₁.size)
    (h : HWP P host s (fr accMi L) (vals (Val.i64 (dw B₁ n) :: vs).reverse ++ rest) Q) :
    HWP P host s (fr accMi L) (vals (Val.i32 a :: vs).reverse ++ .plain ld64 :: rest) Q := by
  subst ha
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  have hl : Memory.load B₁ (effAddr a.toNat ⟨3, 0⟩) (IntType.i64.width / 8) = some (dw B₁ a.toNat) :=
    load_dw (B := B₁) (by simp only [effAddr]; exact hb)
  have key : ∀ w : BitVec 64, w = dw B₁ a.toNat →
      HWP P host s (fr accMi L) (vals (vs.reverse ++ [Val.num ⟨.int .i64, w⟩]) ++ rest) Q := by
    rintro w rfl
    exact h
  exact Wp.intLoad (m := .part) (a := .i32) (i := a) hA.mem1 hl (key _ (setWidth64 _))

/-- `global.set 4` (the heap pointer). -/
theorem w_gsetHeap (hA : InA top B₁ s) {v : BitVec 32}
    (h : ∀ s', HWP P host s' (fr accMi L) (vals vs.reverse ++ rest) Q) :
    HWP P host s (fr accMi L) (vals (Val.i32 v :: vs).reverse ++ .plain (gset gHeap) :: rest) Q := by
  rw [vals_rev_cons, show vals vs.reverse ++ [(Val.i32 v).toAdmin] =
    vals (vs.reverse ++ [Val.i32 v]) by simp]
  exact Wp.globalSet (m := .part) hA.glob4 (h _)

/-- `drop`. -/
theorem w_drop {f : Frame} {v : Val} (h : HWP P host s f (vals vs.reverse ++ rest) Q) :
    HWP P host s f (vals (v :: vs).reverse ++ .plain .drop :: rest) Q := by
  rw [vals_rev_push]
  exact Wp.drop (m := .part) h

/-- The postcondition of the check's body: one result, nonzero only if `Goal`. -/
def checkPost (Goal : Prop) : Store Nat → Outcome → Prop :=
  fun _ o => ∀ r : BitVec 32, o = .normal [Val.i32 r] → r ≠ 0#32 → Goal

/-- **The end of the check**: `top := heapBase`, then answer local `8`. -/
theorem w_tail {Goal : Prop} (hA : InA top B₁ s) (hL : 8 < L.length)
    (hg : L.getD 8 0 ≠ 0#32 → Goal) :
    HWP P host s (fr accMi L) (vals ([] : List Val).reverse ++
      [.plain (c32 heapBase), .plain (gset gHeap), .plain (lget 8)]) (bodyPost 1 (checkPost Goal)) := by
  refine w_const ?_
  refine w_gsetHeap hA fun s' => ?_
  refine w_lget hL (by decide) ?_
  refine w_end ⟨rfl, fun r hr hne => hg ?_⟩
  obtain ⟨⟩ := hr
  exact hne

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
