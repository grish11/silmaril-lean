module

public import Silmaril.Proofs.Sim.RV64.Mem.Sound

/-!
# The memory-state RV64 simulator: loading a reference state and a program

`img σ ws` is one page holding the register state `σ` (Linux riscv `user_regs_struct` layout)
and the program `ws` at `0x1000`. **`absState_img`**: its abstraction is `σ` (for `σ` with the
unobservable `x0` slot zero); **`absCode_img`**: its code is `codeAt 0x1000 ws`; `wf_img`.
Every reference state and program is therefore loadable into the simulator.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Mem

open Silmaril.Wasm.Logic.Core (leNat bytesAt)
open Silmaril.Sim.RV64
open Silmaril.RiscV (State Word)

theorem img_size (σ : State) (ws : List (BitVec 32)) : (img σ ws).size = 65536 := by
  simp [img, ByteArray.size]

theorem wf_img (σ : State) (ws : List (BitVec 32)) : WF (img σ ws) := by
  simp [WF, img_size]

theorem bytesAt_img (σ : State) (ws : List (BitVec 32)) (a n : Nat) (h : a + n ≤ 65536) :
    bytesAt (img σ ws) ⟨a, n⟩ = (List.range n).map fun k => imgByte σ ws (a + k) := by
  apply List.ext_getElem?
  intro i
  rw [Silmaril.Wasm.Logic.Core.getElem?_bytesAt]
  simp only [img, List.getElem?_map]
  by_cases hi : i < n
  · simp [hi, show a + i < 65536 by omega]
  · simp [hi]

theorem leNat_byteOf (v n : Nat) :
    leNat ((List.range n).map fun k => byteOf v k) = v % 256 ^ n := by
  rw [← Silmaril.Wasm.Logic.Core.leNat_encodeLE n v, Silmaril.Wasm.Logic.Core.toList_encodeLE]
  rfl

theorem ld64_img (σ : State) (ws : List (BitVec 32)) (r : Nat) (hr : r < 32) :
    ld64 (img σ ws) (8 * r) = slotVal σ r := by
  rw [ld64, bytesAt_img σ ws _ _ (by omega)]
  have : (List.range 8).map (fun k => imgByte σ ws (8 * r + k)) =
      (List.range 8).map fun k => byteOf (slotVal σ r).toNat k := by
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    simp only [imgByte, show 8 * r + k < 256 by omega, ite_true,
      show (8 * r + k) / 8 = r by omega, show (8 * r + k) % 8 = k by omega]
  rw [this, leNat_byteOf]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := (slotVal σ r).isLt
  omega

theorem ld64_img_end (σ : State) (ws : List (BitVec 32)) :
    ld64 (img σ ws) 264 = BitVec.ofNat 64 (4096 + 4 * ws.length) := by
  rw [ld64, bytesAt_img σ ws _ _ (by omega)]
  have : (List.range 8).map (fun k => imgByte σ ws (264 + k)) =
      (List.range 8).map fun k => byteOf (4096 + 4 * ws.length) k := by
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    simp only [imgByte, show ¬ 264 + k < 256 by omega, ite_false,
      show 264 ≤ 264 + k ∧ 264 + k < 272 from ⟨by omega, by omega⟩, ite_true,
      show 264 + k - 264 = k by omega, and_self]
  rw [this, leNat_byteOf]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem ld32_img (σ : State) (ws : List (BitVec 32)) (j : Nat) (hj : j < ws.length)
    (h : 4096 + 4 * ws.length ≤ 65536) :
    ld32 (img σ ws) (4096 + 4 * j) = ws[j] := by
  rw [ld32, bytesAt_img σ ws _ _ (by omega)]
  have : (List.range 4).map (fun k => imgByte σ ws (4096 + 4 * j + k)) =
      (List.range 4).map fun k => byteOf (ws[j]).toNat k := by
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    simp only [imgByte, show ¬ 4096 + 4 * j + k < 256 by omega, ite_false,
      show ¬ (264 ≤ 4096 + 4 * j + k ∧ 4096 + 4 * j + k < 272) by omega,
      show 4096 ≤ 4096 + 4 * j + k ∧ 4096 + 4 * j + k < 4096 + 4 * ws.length from
        ⟨by omega, by omega⟩, ite_true,
      show (4096 + 4 * j + k - 4096) / 4 = j by omega,
      show (4096 + 4 * j + k - 4096) % 4 = k by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some, and_self]
  rw [this, leNat_byteOf]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := (ws[j]).isLt
  omega

/-- **Loading a state**: the abstraction of the image is the state (whose unobservable `x0`
slot is zero). -/
theorem absState_img (σ : State) (ws : List (BitVec 32)) (h0 : σ.regs 0#5 = 0) :
    absState (img σ ws) = σ := by
  have hpc : ld64 (img σ ws) 0 = σ.pc := by
    simpa [slotVal] using ld64_img σ ws 0 (by omega)
  cases σ with
  | mk regs pc =>
    simp only [absState, State.mk.injEq]
    refine ⟨?_, hpc⟩
    funext r
    by_cases hr : r = 0#5
    · subst hr; simpa using h0.symm
    · rw [ite_eq_right hr, ld64_img _ ws r.toNat r.isLt]
      have hr' : r.toNat ≠ 0 := fun h => hr (BitVec.eq_of_toNat_eq (by simpa using h))
      simp [slotVal, hr']

/-- **Loading a program**: the code of the image is `codeAt 0x1000 ws`. -/
theorem absCode_img (σ : State) (ws : List (BitVec 32)) (h : 4096 + 4 * ws.length ≤ 65536) :
    absCode (img σ ws) = codeAt 4096 ws := by
  have hend : codeEnd (img σ ws) = 4096 + 4 * ws.length := by
    simp only [codeEnd, ld64_img_end σ ws, BitVec.toNat_ofNat]; omega
  funext pc
  simp only [absCode, codeAt, hend]
  by_cases ha : 4096 ≤ pc.toNat ∧ (pc.toNat - 4096) % 4 = 0
  · rw [ite_eq_left ha]
    by_cases hin : pc.toNat + 4 ≤ 4096 + 4 * ws.length
    · rw [ite_eq_left ⟨by omega, ha.1, hin, h⟩]
      have hj : (pc.toNat - 4096) / 4 < ws.length := by omega
      have := ld32_img σ ws _ hj h
      rw [show 4096 + 4 * ((pc.toNat - 4096) / 4) = pc.toNat by omega] at this
      rw [List.getElem?_eq_getElem hj, this]
    · rw [ite_eq_right (by omega), List.getElem?_eq_none (by omega)]
  · rw [ite_eq_right ha, ite_eq_right (by omega)]

end Silmaril.Sim.RV64.Mem
