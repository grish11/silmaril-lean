module

public import Silmaril.Sim.RV64.Example.Defs
public import Silmaril.Sim.RV64.Reduce.Thms

/-!
# An RV64 problem solved as a Wasm problem: per-instruction conditions by specialisation

`post_add`, `post_addi`, `post_stop`: the per-instruction obligations of the Wasm problem,
discharged through the specialised semantics of `step` (`Silmaril.Sim.RV64.Reduce.triple_of_stepPost`):
the fetched word is evaluated by `decode` (`decide`), and the obligation is register arithmetic
on the abstraction. The simulator's dispatch is never unfolded (it was verified once, in
`step_sound`). The earlier route, symbolic execution of the whole body by `wpc` per
instruction, took ~75 s per instruction; this file checks in ~5 s.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Example

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem Silmaril.Sim.RV64.Reduce
open Silmaril.Wasm.Logic.Words (SameOutside)
open Silmaril.RiscV (decode State)

theorem decode_add : decode 0x00b50533#32 = some (.reg .add 10#5 10#5 11#5) := by decide
theorem decode_addi : decode 0x00150513#32 = some (.imm .add 10#5 10#5 1#12) := by decide

/-- The invariant is kept outside the register block. -/
theorem inv_frame {x y : BitVec 64} {j : Nat} {B B' : ByteArray} (h : progInv x y j B)
    (hso : SameOutside B B' 0 256) :
    65536 ≤ B'.size ∧ ld64 B' 264 = 4104#64 ∧ ld32 B' 4096 = 0x00b50533#32 ∧
      ld32 B' 4100 = 0x00150513#32 := by
  obtain ⟨hB, hend, hw0, hw1, -⟩ := h
  exact ⟨hso.1 ▸ hB, (ld64_after hso 264 (by omega)).trans hend,
    (ld32_after hso 4096 (by omega)).trans hw0, (ld32_after hso 4100 (by omega)).trans hw1⟩

theorem ld64_reg (B : ByteArray) (r : Nat) (hr : 0 < r) (hr' : r < 32) :
    ld64 B (8 * r) = (absState B).regs (BitVec.ofNat 5 r) := by
  rw [absState_regs B _ (by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega)]
  simp; congr 1; omega

/-- `add a0, a0, a1` at `0x1000`. -/
theorem post_add (x y : BitVec 64) (B : ByteArray) (st : BitVec 32) (B' : ByteArray)
    (hI : progInv x y 0 B) (h : StepPost B st B') : st = 0 ∧ progInv x y 1 B' := by
  have hI' := hI
  obtain ⟨hB, hend, hw0, -, hpc, hy, hx⟩ := hI
  have hw := fetched_word (pc := 4096) (en := 4104) hpc hend hw0 (by decide) le_rfl
    (by decide) (by decide)
  obtain ⟨rfl, hs, hso⟩ := retire_of_word hw decode_add h
  obtain ⟨hB', hend', hw0', hw1'⟩ := inv_frame hI' hso
  refine ⟨rfl, hB', hend', hw0', hw1', ?_, ?_, ?_⟩
  · rw [← absState_pc, hs, Silmaril.RiscV.step_pc, absState_pc, hpc]; rfl
  · rw [ld64_reg B' 11 (by omega) (by omega), hs, ← hy, ld64_reg B 11 (by omega) (by omega)]
    simp [Silmaril.RiscV.step, Silmaril.RiscV.State.write, Silmaril.RiscV.Instr.dest,
      Silmaril.Machine.RegisterFile.write]
  · rw [ld64_reg B' 10 (by omega) (by omega), hs]
    have h10 := ld64_reg B 10 (by omega) (by omega)
    have h11 := ld64_reg B 11 (by omega) (by omega)
    simp only [Nat.reduceMul] at h10 h11
    simp [Silmaril.RiscV.step, Silmaril.RiscV.State.write, Silmaril.RiscV.Instr.dest,
      Silmaril.RiscV.Instr.value, Silmaril.RiscV.RegOp.eval, Silmaril.RiscV.State.read,
      Silmaril.Machine.RegisterFile.write, ← h10, ← h11, hx, hy]

/-- `addi a0, a0, 1` at `0x1004`. -/
theorem post_addi (x y : BitVec 64) (B : ByteArray) (st : BitVec 32) (B' : ByteArray)
    (hI : progInv x y 1 B) (h : StepPost B st B') : st = 0 ∧ progInv x y 2 B' := by
  have hI' := hI
  obtain ⟨hB, hend, -, hw1, hpc, hy, hx⟩ := hI
  have hw := fetched_word (pc := 4100) (en := 4104) hpc hend hw1 (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨rfl, hs, hso⟩ := retire_of_word hw decode_addi h
  obtain ⟨hB', hend', hw0', hw1'⟩ := inv_frame hI' hso
  refine ⟨rfl, hB', hend', hw0', hw1', ?_, ?_, ?_⟩
  · rw [← absState_pc, hs, Silmaril.RiscV.step_pc, absState_pc, hpc]; rfl
  · rw [ld64_reg B' 11 (by omega) (by omega), hs, ← hy, ld64_reg B 11 (by omega) (by omega)]
    simp [Silmaril.RiscV.step, Silmaril.RiscV.State.write, Silmaril.RiscV.Instr.dest,
      Silmaril.Machine.RegisterFile.write]
  · rw [ld64_reg B' 10 (by omega) (by omega), hs]
    have h10 := ld64_reg B 10 (by omega) (by omega)
    simp only [Nat.reduceMul] at h10
    simp [Silmaril.RiscV.step, Silmaril.RiscV.State.write, Silmaril.RiscV.Instr.dest,
      Silmaril.RiscV.Instr.value, Silmaril.RiscV.ImmOp.eval, Silmaril.RiscV.State.read,
      Silmaril.Machine.RegisterFile.write, ← h10, hx]

/-- At `0x1008 = code_end` the fetch faults: the call stops. -/
theorem post_stop (x y : BitVec 64) (B : ByteArray) (st : BitVec 32) (B' : ByteArray)
    (hI : progInv x y 2 B) (h : StepPost B st B') : st ≠ 0 := by
  obtain ⟨-, hend, -, -, hpc, -⟩ := hI
  have hn : absCode B (ld64 B 0) = none := by
    have hp : (ld64 B 0).toNat = 4104 := by rw [hpc]; rfl
    have hc : codeEnd B = 4104 := by simp only [codeEnd, hend]; rfl
    simp only [absCode, hp, hc]
    rw [ite_eq_right (by omega)]
  rcases h with ⟨-, hs, -⟩ | ⟨h23, -, -⟩
  · simp [refStep, absState_pc, hn] at hs
  · rcases h23 with rfl | rfl <;> decide

end Silmaril.Sim.RV64.Example
