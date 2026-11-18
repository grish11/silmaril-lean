module

public import Silmaril.Sim.RV64.Sym.Defs

/-!
# The symbolic executor is sound

**`extSym_sound`**: if `extSym code n pc regs = some T`, then from every `Ext` machine state
whose memory fetches `code`, whose `pc` is `pc` and whose registers are the values of `regs` for
the entry values `σ` (with `σ ra` four-byte aligned), the machine retires to `σ ra` with
`a0 = T.eval σ` and the callee-saved registers at their entry values. Proved once, by
induction on the fuel: `symValue_sound` per register-only instruction, `jumpTo` for branches
and the return.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Sym

open Silmaril.RiscV.Ext
open Silmaril.RiscV (State)

theorem stepOpt_of {m m' : MState} {w : BitVec 32} {i : Instr}
    (hf : fetch m.memory m.core.pc = some w) (hd : decode w = some i)
    (he : i.exec m = .retired m') : m.stepOpt = some m' := by
  simp [MState.stepOpt, MState.step, hf, hd, he]

theorem symValue_sound {c : Compute} {pc : W64} {regs : Reg → E} {e : E} {s : State}
    {σ : Reg → W64} (h : symValue c pc regs = some e) (hpc : s.pc = pc)
    (hr : ∀ r, s.read r = (regs r).eval σ) : c.value s = e.eval σ := by
  match c, h with
  | .base (.imm op _ rs1 imm), h =>
    rw [← Option.some.inj h]
    cases op <;> simp [Compute.value, Silmaril.RiscV.Instr.value, Silmaril.RiscV.ImmOp.eval,
      E.eval, Bin.eval, immBin, hr]
  | .base (.reg op _ rs1 rs2), h =>
    rw [← Option.some.inj h]
    cases op <;> simp [Compute.value, Silmaril.RiscV.Instr.value, Silmaril.RiscV.RegOp.eval,
      Silmaril.RiscV.ShiftOp.eval, E.eval, Bin.eval, regBin, hr]
  | .base (.shift op _ rs1 amt), h =>
    rw [← Option.some.inj h]
    have ha : (amt.setWidth 64).setWidth 6 = amt := by
      apply BitVec.eq_of_toNat_eq; simp
    cases op <;> simp [Compute.value, Silmaril.RiscV.Instr.value, Silmaril.RiscV.ShiftOp.eval,
      E.eval, Bin.eval, shiftBin, hr, ha]
  | .base (.upper op _ imm), h =>
    rw [← Option.some.inj h]
    simp [Compute.value, Silmaril.RiscV.Instr.value, E.eval, hpc]
  | .mulDiv .mul _ rs1 rs2, h =>
    rw [← Option.some.inj h]
    simp [Compute.value, MulOp.eval, E.eval, Bin.eval, hr]
  | .mulDiv .remu _ rs1 rs2, h =>
    rw [← Option.some.inj h]
    simp [Compute.value, MulOp.eval, E.eval, Bin.eval, hr]

theorem upd_sound {s : State} {regs : Reg → E} {σ : Reg → W64} (hr : ∀ r, s.read r = (regs r).eval σ)
    (d : Reg) (e : E) : ∀ r, (s.write d (e.eval σ)).read r = (upd regs d e r).eval σ := by
  intro r
  by_cases hd : d = 0#5
  · subst hd; simp [upd, hr]
  · by_cases hrd : r = d
    · subst hrd
      rw [State.read_write_same _ _ _ hd]
      simp [upd, hd]
    · rw [State.read_write_other _ _ _ _ hrd]
      simp [upd, hd, hrd, hr]

theorem ret_target (r : W64) (h : r.toNat % 4 = 0) :
    (r + (0#12).signExtend 64) &&& ~~~1#64 = r := by
  have h0 : r.getLsbD 0 = false := by
    simp [BitVec.getLsbD, Nat.testBit]; omega
  rw [show (0#12).signExtend 64 = 0#64 by decide, BitVec.add_zero]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_one]
  rcases Nat.eq_zero_or_pos i with rfl | hp
  · simp [← BitVec.getLsbD_eq_getElem, h0]
  · simp [show i ≠ 0 by omega]

/-- **Soundness of the symbolic executor.** -/
theorem extSym_sound (code : Code) (M : Silmaril.Process.Memory)
    (hcode : ∀ p w, code p = some w → fetch M p = some w) (σ : Reg → W64)
    (hra : (σ 1#5).toNat % 4 = 0) :
    ∀ (n : Nat) (pc : W64) (regs : Reg → E) (T : Tree) (m : MState),
      extSym code n pc regs = some T → m.memory = M → m.core.pc = pc →
      (∀ r, m.core.read r = (regs r).eval σ) →
      ∃ k m', Silmaril.Machine.Execution.run MState.stepOpt k m = some m' ∧
        m'.core.pc = σ 1#5 ∧ m'.core.read 10#5 = T.eval σ ∧
        ∀ r ∈ calleeSaved, m'.core.read r = σ r
  | 0, _, _, _, _, h, _, _, _ => by simp [extSym] at h
  | n + 1, pc, regs, T, m, h, hM, hpc, hr => by
    simp only [extSym] at h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hd, h⟩ := Option.bind_eq_some_iff.mp h
    have hf : fetch m.memory m.core.pc = some w := by rw [hM, hpc]; exact hcode _ _ hw
    cases i with
    | compute c =>
      dsimp only at h
      obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
      have hv := symValue_sound he hpc hr
      let m1 : MState := { m with core := c.step m.core }
      have s1 : m.stepOpt = some m1 := stepOpt_of hf hd rfl
      have hr1 : ∀ r, m1.core.read r = (upd regs c.dest e r).eval σ := by
        intro r
        have := upd_sound hr c.dest e r
        rw [← hv] at this
        show (m.core.write c.dest (c.value m.core)).read r = _
        exact this
      obtain ⟨k, m', hrun, h1, h2, h3⟩ :=
        extSym_sound code M hcode σ hra n (pc + 4) _ T m1 h hM (by simp [m1, Compute.step, hpc]) hr1
      exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], h1, h2, h3⟩
    | branch op rs1 rs2 half =>
      dsimp only at h
      split at h
      next hal =>
        obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨f, hf', rfl⟩ := Option.map_eq_some_iff.mp h
        have hc : op.eval (m.core.read rs1) (m.core.read rs2) =
            op.eval ((regs rs1).eval σ) ((regs rs2).eval σ) := by rw [hr, hr]
        by_cases hb : op.eval ((regs rs1).eval σ) ((regs rs2).eval σ)
        · let m1 : MState := { m with core := { m.core with pc := pc + branchOffset half } }
          have s1 : m.stepOpt = some m1 := by
            refine stepOpt_of hf hd ?_
            simp only [Instr.exec, hc, hb, ite_true, jumpTo, hpc, hal, m1]
          obtain ⟨k, m', hrun, h1, h2, h3⟩ :=
            extSym_sound code M hcode σ hra n _ regs t m1 ht hM rfl (fun r => hr r)
          refine ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], h1, ?_, h3⟩
          simp [Tree.eval, hb, h2]
        · let m1 : MState := { m with core := { m.core with pc := pc + 4 } }
          have s1 : m.stepOpt = some m1 := by
            refine stepOpt_of hf hd ?_
            simp only [Instr.exec, hc, hb, Bool.false_eq_true, ite_false, hpc, m1]
          obtain ⟨k, m', hrun, h1, h2, h3⟩ :=
            extSym_sound code M hcode σ hra n _ regs f m1 hf' hM rfl (fun r => hr r)
          refine ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], h1, ?_, h3⟩
          simp [Tree.eval, hb, h2]
      next => cases h
    | jalr rd rs1 off =>
      dsimp only at h
      split at h
      next hc =>
        obtain ⟨rfl, rfl, rfl, h1, h2⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        have hra' : m.core.read 1#5 = σ 1#5 := by rw [hr, h1]; rfl
        let m1 : MState := { m with core := { m.core with pc := σ 1#5 } }
        have s1 : m.stepOpt = some m1 := by
          refine stepOpt_of hf hd ?_
          have ht : jalrTarget m.core 1#5 0#12 = σ 1#5 := by
            rw [jalrTarget, effectiveAddress, hra']; exact ret_target _ hra
          simp only [Instr.exec, jumpTo, ht, hra, ite_true, State.write_zero, m1]
        refine ⟨1, m1, by simp [Silmaril.Machine.Execution.run, s1], rfl, ?_, ?_⟩
        · show m.core.read 10#5 = _
          rw [hr]; rfl
        · intro r hrm
          show m.core.read r = σ r
          have := List.all_eq_true.mp h2 r hrm
          simp only [beq_iff_eq] at this
          rw [hr, this]; rfl
      next => cases h
    | load => cases h
    | store => cases h
    | jal => cases h
    | ebreak => cases h

/-- The entry register file matches every state. -/
theorem regs0_eval (s : State) (r : Reg) :
    s.read r = (regs0 r).eval (fun q => s.read q) := by
  by_cases h : r = 0#5
  · subst h; simp [regs0, E.eval]
  · simp [regs0, h, E.eval]

/-- The value of a tree depends only on its variables. -/
theorem E.eval_congr {σ τ : Reg → W64} : ∀ (e : E), (∀ r ∈ e.vars, σ r = τ r) → e.eval σ = e.eval τ
  | .var r, h => h r (by simp [E.vars])
  | .const _, _ => rfl
  | .bin op a b, h => by
    simp only [E.eval]
    rw [E.eval_congr a fun r hr => h r (by simp [E.vars, hr]),
      E.eval_congr b fun r hr => h r (by simp [E.vars, hr])]

theorem Tree.eval_congr {σ τ : Reg → W64} {ps : List Reg} (hps : ∀ r ∈ ps, σ r = τ r) :
    ∀ (t : Tree), t.varsIn ps = true → t.eval σ = t.eval τ
  | .ret a0, h => by
    simp only [Tree.varsIn, List.all_eq_true, decide_eq_true_eq] at h
    exact E.eval_congr a0 fun r hr => hps r (h r hr)
  | .br op a b t f, h => by
    simp only [Tree.varsIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ha, hb⟩, ht⟩, hf⟩ := h
    simp only [Tree.eval]
    rw [E.eval_congr a fun r hr => hps r (ha r hr), E.eval_congr b fun r hr => hps r (hb r hr),
      Tree.eval_congr hps t ht, Tree.eval_congr hps f hf]

end Silmaril.Sim.RV64.Sym
