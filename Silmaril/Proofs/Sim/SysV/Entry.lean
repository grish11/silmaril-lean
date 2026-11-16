module

public import Silmaril.Sim.SysV.Defs

/-!
# The entry state of a call

* `pushAll_state`, `pushAll_regions`: pushing `k` words lowers `rsp` by `8 k` and keeps the
  memory map.
* `setup_core`: the registers of the set-up state are `entryCore` (a function of the caller's
  registers only).
* `entrySp_mod`: the entry stack pointer is `≡ 8 (mod 16)`.
* `setup_ret`: the sentinel is readable at the entry stack pointer.
* **`setup_abiEntry`**: the set-up state meets `FnContract.AbiEntry`, with return address
  `SENTINEL` (`setup_retOf`).
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine.X86.FnContract (AbiEntry)

theorem write_write (σ : State) (r : Reg) (v w : Word) : (σ.write r v).write r w = σ.write r w := by
  simp [State.write, Silmaril.Machine.RegisterFile.write_shadow]

private theorem write_rsp_zero (σ : State) :
    σ.write .rsp (σ.read .rsp - BitVec.ofNat 64 (8 * ([] : List Word).length)) = σ := by
  simp only [List.length_nil, Nat.mul_zero]
  rw [show σ.read .rsp - BitVec.ofNat 64 0 = σ.read .rsp by simp]
  simp [State.write, State.read, Silmaril.Machine.RegisterFile.write_current]

theorem pushAll_state {vs : List Word} {σ σ' : State} {m m' : Memory}
    (h : pushAll vs σ m = some (σ', m')) :
    σ' = σ.write .rsp (σ.read .rsp - BitVec.ofNat 64 (8 * vs.length)) ∧ m'.regions = m.regions := by
  induction vs generalizing σ m with
  | nil =>
    have h' : σ = σ' ∧ m = m' := by simpa only [pushAll, Option.some.injEq, Prod.mk.injEq] using h
    exact ⟨by rw [← h'.1, write_rsp_zero], by rw [← h'.2]⟩
  | cons v vs ih =>
    obtain ⟨⟨t, mt⟩, hp, hr⟩ : ∃ a : State × Memory, Silmaril.X86.pushWord σ m v = some a ∧
        pushAll vs a.1 a.2 = some (σ', m') := by
      simpa only [pushAll, Option.bind_eq_some_iff] using h
    obtain ⟨hσ', hreg⟩ : σ' = t.write .rsp (t.read .rsp - BitVec.ofNat 64 (8 * vs.length)) ∧
        m'.regions = mt.regions := ih hr
    have ht : t = σ.write .rsp (σ.read .rsp - 8#64) := Silmaril.X86.pushWord_state hp
    have hw : mt.regions = m.regions := (Silmaril.X86.pushWord_writesOnly hp).1
    refine ⟨?_, hreg.trans hw⟩
    rw [hσ', ht, write_write, State.read_write_same]
    congr 1
    simp only [List.length_cons]
    bv_omega

theorem setArgs_read_other (as : List Word) (rs : List Reg) (σ : State) (r : Reg) (h : r ∉ rs) :
    (setArgs as rs σ).read r = σ.read r := by
  induction as generalizing rs σ with
  | nil => cases rs <;> rfl
  | cons a as ih =>
    cases rs with
    | nil => rfl
    | cons q rs =>
      simp only [List.mem_cons, not_or] at h
      simp only [setArgs]
      rw [ih rs _ h.2, State.read_write_other _ _ _ _ h.1]

theorem rsp_not_mem_intArgRegs : Reg.rsp ∉ Silmaril.X86.sysv64.intArgRegs := by decide

@[deprecated rsp_not_mem_intArgRegs (since := "2026-11-10")]
alias rsp_not_mem_gpArguments := rsp_not_mem_intArgRegs

theorem alignDown16_toNat (y : Word) : (alignDown16 y).toNat = y.toNat - y.toNat % 16 := by
  have h : (y &&& 15#64).toNat = y.toNat % 16 := by
    rw [BitVec.toNat_and]
    have : (15#64).toNat = 2 ^ 4 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  have hy := y.isLt
  rw [alignDown16, BitVec.toNat_sub, h]
  omega

/-- The entry stack pointer is `8 mod 16`. -/
theorem entrySp_mod (n : Nat) (rsp : Word) : (entrySp n rsp).toNat % 16 = 8 := by
  have h := alignDown16_toNat (rsp - BitVec.ofNat 64 (8 * n))
  have hy := (alignDown16 (rsp - BitVec.ofNat 64 (8 * n))).isLt
  have hz := (rsp - BitVec.ofNat 64 (8 * n)).isLt
  rw [entrySp, BitVec.toNat_sub, h]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The shape of a successful setup. -/
theorem setup_some {d : SysVCall} {m e : MState} (h : setup d m = some e) :
    ∃ σ₁ m₁ σ₂,
      pushAll d.stackArgs.reverse (m.core.write .rsp
        (alignDown16 (m.core.read .rsp - BitVec.ofNat 64 (8 * d.stackArgs.length)) +
          BitVec.ofNat 64 (8 * d.stackArgs.length))) m.memory = some (σ₁, m₁) ∧
      Silmaril.X86.pushWord σ₁ m₁ SENTINEL = some (σ₂, e.memory) ∧
      e.core = { setArgs d.regArgs Silmaril.X86.sysv64.intArgRegs σ₂ with rip := d.target } := by
  simp only [setup, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨σ₁, m₁⟩, h₁, ⟨σ₂, m₂⟩, h₂, rfl⟩ := h
  exact ⟨σ₁, m₁, σ₂, h₁, h₂, rfl⟩

/-- The stack pointer before the sentinel push is the aligned `S`, and after it `entrySp`. -/
theorem setup_rsp {d : SysVCall} {m : MState} {σ₁ σ₂ : State} {m₁ m₂ : Memory}
    (h₁ : pushAll d.stackArgs.reverse (m.core.write .rsp
        (alignDown16 (m.core.read .rsp - BitVec.ofNat 64 (8 * d.stackArgs.length)) +
          BitVec.ofNat 64 (8 * d.stackArgs.length))) m.memory = some (σ₁, m₁))
    (h₂ : Silmaril.X86.pushWord σ₁ m₁ SENTINEL = some (σ₂, m₂)) :
    σ₁.read .rsp - 8#64 = entrySp d.stackArgs.length (m.core.read .rsp) ∧
      σ₂ = m.core.write .rsp (entrySp d.stackArgs.length (m.core.read .rsp)) ∧
      m₁.regions = m.memory.regions := by
  obtain ⟨rfl, hreg⟩ := pushAll_state h₁
  have h₂' := Silmaril.X86.pushWord_state h₂
  have hsp : ((m.core.write .rsp
      (alignDown16 (m.core.read .rsp - BitVec.ofNat 64 (8 * d.stackArgs.length)) +
        BitVec.ofNat 64 (8 * d.stackArgs.length))).write .rsp
      (alignDown16 (m.core.read .rsp - BitVec.ofNat 64 (8 * d.stackArgs.length)) +
        BitVec.ofNat 64 (8 * d.stackArgs.length) -
        BitVec.ofNat 64 (8 * d.stackArgs.reverse.length))).read .rsp - 8#64 =
      entrySp d.stackArgs.length (m.core.read .rsp) := by
    rw [State.read_write_same, List.length_reverse, entrySp]
    bv_omega
  refine ⟨?_, ?_, hreg⟩
  · rw [State.read_write_same, write_write, State.read_write_same] at *
    exact hsp
  · rw [h₂']
    simp only [State.read_write_same, write_write] at hsp ⊢
    rw [hsp]

/-- **The registers of the entry state.** -/
theorem setup_core {d : SysVCall} {m e : MState} (h : setup d m = some e) :
    e.core = entryCore d m.core := by
  obtain ⟨σ₁, m₁, σ₂, h₁, h₂, he⟩ := setup_some h
  obtain ⟨-, rfl, -⟩ := setup_rsp h₁ h₂
  rw [he, entryCore]

/-- The sentinel is readable at the entry stack pointer. -/
theorem setup_ret {d : SysVCall} {m e : MState} (h : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8) :
    e.memory.readBytes (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8 =
      some (encodeWords [SENTINEL]) := by
  obtain ⟨σ₁, m₁, σ₂, h₁, h₂, -⟩ := setup_some h
  obtain ⟨hsp, -, hreg⟩ := setup_rsp h₁ h₂
  have hr' : m₁.Permitted .read (σ₁.read .rsp - 8#64).toNat 8 := by
    rw [hsp]
    unfold Memory.Permitted at hr ⊢
    rw [Silmaril.X86.Memory.checkSpan_congr hreg]
    exact hr
  have := Silmaril.X86.pushWord_readBytes h₂ hr'
  rw [hsp] at this
  exact this

theorem entryCore_rsp (d : SysVCall) (σ : State) :
    (entryCore d σ).read .rsp = entrySp d.stackArgs.length (σ.read .rsp) := by
  show (setArgs d.regArgs Silmaril.X86.sysv64.intArgRegs _).read .rsp = _
  rw [setArgs_read_other _ _ _ _ rsp_not_mem_intArgRegs, State.read_write_same]

theorem setup_retOf {d : SysVCall} {m e : MState} (h : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8) :
    Silmaril.Machine.X86.Open.retOf e.core e.memory = SENTINEL := by
  rw [Silmaril.Machine.X86.Open.retOf, setup_core h, entryCore_rsp, setup_ret h hr]
  simp

/-- **The set-up state meets the System V entry obligations.** -/
theorem setup_abiEntry {d : SysVCall} {m e : MState} (h : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8) :
    AbiEntry e.core e.memory where
  aligned := by rw [setup_core h, entryCore_rsp]; exact entrySp_mod _ _
  returnAddress := by
    rw [setup_retOf h hr, setup_core h, entryCore_rsp]
    exact setup_ret h hr

end Silmaril.Sim.SysV
