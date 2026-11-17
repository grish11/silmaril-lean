module

public import Silmaril.Proofs.Wasm.Examples.FarkasAccept.Abi

@[expose] public section

/-!
# The acceptor's `check`, every run

`check_hwp`: from any store of the acceptor (`AccStore`: any checker state, any heap pointer,
the ABI memory `B₁`), with the records of the system and the multipliers in bounds, every run of
the body of `check(sp, sl, yp, yl)` returns one value, and a nonzero value only if
`systemAt B₁ sp sl ∈ Infeasible`.

The reset (`check()`, answer dropped) leaves the checker representing no rows (`RepA []`). The
row loop keeps `RowInv`: the store represents rows `rs` that all come from the system
(`Sub`, up to the order of each row's coefficients); the coefficient loop of inequality `i`
keeps `EntInv`: the current row is the inequality's first `k` pairs, reversed, with its bound.
The final `check()` answers nonzero only if the represented rows carry a valid certificate, and
`infeasible_of_sub` concludes. When `yl ≠ sl` the answer is `0`.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.Farkas (Mach)
open Silmaril.Wasm.Examples.LRAT (fr w_lset w_if w_armEnd w_brIf w_br w_while whilePost_exit
  whilePost_cont b32_ne_zero b32_eq_zero)
open Silmaril.Wasm.Examples.Common (bodyPost)
open Silmaril.Wasm.Examples.FarkasAccept (accS AccStore systemAt IneqsIn dw checkBody feedCode
  rowLoopBody entryLoopBody)
open Silmaril.Logic.LinArith (WRows Cmd)
open Silmaril.Logic.LinArith.Carrier (Infeasible)
open Silmaril.Wasm.Logic.Words (wd)

variable {P : Profile} {host : HostSemantics Nat} {top : BitVec 32} {B₁ : ByteArray}

/-- The row loop's invariant. -/
def RowInv (top : BitVec 32) (B₁ : ByteArray) (sp sl yp yl : BitVec 32) :
    Store Nat → Frame → Prop := fun s f =>
  ∃ (i c5 c6 c7 : BitVec 32) (rs : WRows), RepA top B₁ rs s ∧
    Sub (systemAt B₁ sp.toNat sl.toNat) rs ∧
    f = fr accMi [sp, sl, yp, yl, i, c5, c6, c7, 0] ∧ i.toNat ≤ sl.toNat

/-- The coefficient loop's invariant, for inequality `i`. -/
def EntInv (top : BitVec 32) (B₁ : ByteArray) (sp sl yp yl i : BitVec 32) :
    Store Nat → Frame → Prop := fun s f =>
  ∃ (k : BitVec 32) (y : ℤ) (rs : WRows),
    RepA top B₁ ((y, ⟨(decC B₁ (wd B₁ (sp.toNat + 16 * i.toNat)).toNat k.toNat).reverse,
      (dw B₁ (sp.toNat + 16 * i.toNat + 8)).toInt⟩) :: rs) s ∧
    Sub (systemAt B₁ sp.toNat sl.toNat) rs ∧
    f = fr accMi [sp, sl, yp, yl, i, wd B₁ (sp.toNat + 16 * i.toNat),
      wd B₁ (sp.toNat + 16 * i.toNat + 4), k, 0] ∧
    k.toNat ≤ (wd B₁ (sp.toNat + 16 * i.toNat + 4)).toNat

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **`check`, every run.** -/
theorem check_hwp {s : Store Nat} (hS : AccStore s top B₁) {sp sl yp yl : BitVec 32}
    (hsp : IneqsIn B₁ sp.toNat sl.toNat) (hyp : yp.toNat + 8 * yl.toNat ≤ B₁.size) :
    HWP P host s (fr accMi [sp, sl, yp, yl, 0, 0, 0, 0, 0])
      (vals ([] : List Val).reverse ++ expression checkBody ++ [])
      (bodyPost 1 (checkPost (systemAt B₁ sp.toNat sl.toNat ∈ Infeasible))) := by
  have hsz : B₁.size = 1048576 := hS.size₁
  obtain ⟨m, hH, hB⟩ := accStore_holds hS
  simp only [checkBody, expression, List.map_cons, List.map_nil,
    List.append_nil]
  refine w_check (vs := []) ⟨m, hH, hB⟩ fun s₁ v hR₁ _ => ?_
  refine w_drop ?_
  wstep; fnorm
  wstep; fnorm
  wstep
  refine w_if (rs := []) (fun hc => ?_) (fun _ => ?_)
  · have hyl : yl = sl := b32_ne_zero.1 hc
    have hyp' : yp.toNat + 8 * sl.toNat ≤ B₁.size := hyl ▸ hyp
    simp only [feedCode, expression, List.map_cons, List.map_nil]
    wstep; fnorm
    wstep; fnorm
    refine w_while (Inv := RowInv top B₁ sp sl yp yl)
      ⟨0, 0, 0, 0, [], hR₁, Sub.nil _, rfl, by simp⟩ ?_
    rintro s f ⟨i, c5, c6, c7, rs, hR, hsub, rfl, hi⟩
    simp only [rowLoopBody, expression, List.map_cons, List.map_nil]
    wstep; fnorm
    wstep; fnorm
    wstep
    refine w_brIf (fun hx => ?_) (fun hx => ?_)
    · -- the end of the system: the final check
      refine w_br (whilePost_exit ?_)
      refine w_check (vs := []) hR.sized fun s₂ v₂ hR₂ hc₂ => ?_
      wstep; fnorm
      refine w_armEnd ?_
      exact w_tail hR₂.inA (by simp) fun hv => infeasible_of_sub hsub (hc₂ rs hR hv)
    · -- one more inequality
      have hlt : i.toNat < sl.toNat := by have := b32_eq_zero.1 hx; omega
      have hsl := hsp.1
      have hc := hsp.2 i.toNat hlt
      -- the multiplier
      wstep; fnorm
      wstep; fnorm
      wstep
      wstep
      wstep
      refine w_ld64 hR.inA (n := yp.toNat + 8 * i.toNat) (by bv_omega) (by omega) ?_
      -- the bound
      wstep; fnorm
      wstep; fnorm
      wstep
      wstep
      wstep
      wstep
      wstep
      refine w_ld64 hR.inA (n := sp.toNat + 16 * i.toNat + 8) (by bv_omega) (by omega) ?_
      refine w_row hR fun s₂ hR₂ => ?_
      -- the coefficient list
      wstep; fnorm
      wstep; fnorm
      wstep
      wstep
      wstep
      refine w_ld1 hR₂.inA (n := sp.toNat + 16 * i.toNat) (by bv_omega) (by omega) ?_
      wstep; fnorm
      wstep; fnorm
      wstep; fnorm
      wstep
      wstep
      wstep
      wstep
      wstep
      refine w_ld1 hR₂.inA (n := sp.toNat + 16 * i.toNat + 4) (by bv_omega) (by omega) ?_
      wstep; fnorm
      wstep; fnorm
      wstep; fnorm
      refine w_while (Inv := EntInv top B₁ sp sl yp yl i)
        ⟨0, _, rs, hR₂, hsub, rfl, by simp⟩ ?_
      rintro s f ⟨k, y, rs', hR', hsub', rfl, hk⟩
      simp only [entryLoopBody, expression, List.map_cons, List.map_nil]
      wstep; fnorm
      wstep; fnorm
      wstep
      refine w_brIf (fun hx => ?_) (fun hx => ?_)
      · -- the end of the inequality: back to the row loop
        have hke : k.toNat = (wd B₁ (sp.toNat + 16 * i.toNat + 4)).toNat := by
          have := b32_ne_zero.1 hx; omega
        refine w_br (whilePost_exit ?_)
        wstep; fnorm
        wstep
        wstep
        wstep; fnorm
        refine w_br (whilePost_cont ⟨_, _, _, _, _, hR', ?_, rfl, ?_⟩)
        · have h := Sub.cons hsub' (mem_systemAt (B := B₁) (p := sp.toNat) hlt) y
          rw [decode_ineqAt] at h
          rw [hke]
          exact h
        · bv_omega
      · -- one more coefficient pair
        have hkl : k.toNat < (wd B₁ (sp.toNat + 16 * i.toNat + 4)).toNat := by
          have := b32_eq_zero.1 hx; omega
        wstep; fnorm
        wstep; fnorm
        wstep
        wstep
        wstep
        refine w_ld1 hR'.inA (n := (wd B₁ (sp.toNat + 16 * i.toNat)).toNat + 16 * k.toNat)
          (by bv_omega) (by omega) ?_
        wstep; fnorm
        wstep; fnorm
        wstep
        wstep
        wstep
        wstep
        wstep
        refine w_ld64 hR'.inA (n := (wd B₁ (sp.toNat + 16 * i.toNat)).toNat + 16 * k.toNat + 8)
          (by bv_omega) (by omega) ?_
        refine w_entry hR' fun s₃ hR₃ => ?_
        wstep; fnorm
        wstep
        wstep
        wstep; fnorm
        refine w_br (whilePost_cont ⟨_, y, rs', ?_, hsub', rfl, by bv_omega⟩)
        have e : (k + BitVec.ofNat 32 1).toNat = k.toNat + 1 := by bv_omega
        rw [e, decC_succ, List.reverse_append, List.reverse_singleton, List.singleton_append]
        exact hR₃
  · exact w_tail hR₁.inA (by simp) fun hv => absurd rfl hv

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
