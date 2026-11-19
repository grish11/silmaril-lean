module

public import Silmaril.Sim.RV64.CfgM.Defs
public import Silmaril.Sim.RV64.Cfg.Thms

/-!
# Cut points with memory reads: soundness

`cfgSymM_sound` (blocks with loads are followed by every concrete `Ext` run whose block outcome
is defined: all loads aligned and readable) and **`reach_blockM`**, as in `Silmaril.Proofs.Sim.RV64.Cfg`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.CfgM

open Silmaril.RiscV.Ext
open Silmaril.RiscV (State)
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym Silmaril.Sim.RV64.Cfg

variable {M : Silmaril.Process.Memory} {σ : Reg → W64}

theorem symValueM_sound {c : Compute} {pc : W64} {regs : Reg → ME} {e : ME} {s : State}
    (h : symValueM c pc regs = some e) (hpc : s.pc = pc)
    (hr : ∀ r, (regs r).eval σ M = some (s.read r)) : e.eval σ M = some (c.value s) := by
  match c, h with
  | .base (.imm op _ rs1 imm), h =>
    rw [← Option.some.inj h]
    cases op <;> simp [Compute.value, Silmaril.RiscV.Instr.value, Silmaril.RiscV.ImmOp.eval,
      ME.eval, Bin.eval, immBin, hr]
  | .base (.reg op _ rs1 rs2), h =>
    rw [← Option.some.inj h]
    cases op <;> simp [Compute.value, Silmaril.RiscV.Instr.value, Silmaril.RiscV.RegOp.eval,
      Silmaril.RiscV.ShiftOp.eval, ME.eval, Bin.eval, regBin, hr]
  | .base (.shift op _ rs1 amt), h =>
    rw [← Option.some.inj h]
    have ha2 : amt.toNat % 64 = amt.toNat := Nat.mod_eq_of_lt (by have := amt.isLt; omega)
    cases op <;> simp [Compute.value, Silmaril.RiscV.Instr.value, Silmaril.RiscV.ShiftOp.eval,
      ME.eval, Bin.eval, shiftBin, hr, ha2]
  | .base (.upper op _ imm), h =>
    rw [← Option.some.inj h]
    simp [Compute.value, Silmaril.RiscV.Instr.value, ME.eval, hpc]
  | .mulDiv .mul _ rs1 rs2, h =>
    rw [← Option.some.inj h]
    simp [Compute.value, MulOp.eval, ME.eval, Bin.eval, hr]
  | .mulDiv .remu _ rs1 rs2, h =>
    rw [← Option.some.inj h]
    simp [Compute.value, MulOp.eval, ME.eval, Bin.eval, hr]

theorem updM_sound {s : State} {regs : Reg → ME} (hr : ∀ r, (regs r).eval σ M = some (s.read r))
    (d : Reg) (e : ME) (v : W64) (hv : e.eval σ M = some v) :
    ∀ r, (updM regs d e r).eval σ M = some ((s.write d v).read r) := by
  intro r
  by_cases hd : d = 0#5
  · subst hd; simp [updM, hr]
  · by_cases hrd : r = d
    · subst hrd
      rw [State.read_write_same _ _ _ hd]
      simp [updM, hd, hv]
    · rw [State.read_write_other _ _ _ _ hrd]
      simp [updM, hd, hrd, hr]

theorem regListM_getD (regs : Reg → ME) (r : Reg) :
    (regListM regs).getD r.toNat (.var r) = regs r := by
  have := r.isLt
  simp [regListM, List.getD_eq_getElem?_getD, this]

theorem abiOKM_spec {regs : Reg → ME} (h : abiOKM regs = true) :
    regs 1#5 = .var 1#5 ∧ ∀ r ∈ calleeSaved, regs r = .var r := by
  simp only [abiOKM, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun r hr => by simpa using h.2 r hr⟩

theorem mapM_regs (regs : Reg → ME) (s : State) (hr : ∀ r, (regs r).eval σ M = some (s.read r)) :
    ∀ l : List Nat, (l.map fun i => regs (BitVec.ofNat 5 i)).mapM (fun e : ME => e.eval σ M) =
      some (l.map fun i => s.read (BitVec.ofNat 5 i))
  | [] => rfl
  | i :: l => by simp [List.mapM_cons, hr, mapM_regs regs s hr l]

theorem vals_of (regs : Reg → ME) (s : State) (hr : ∀ r, (regs r).eval σ M = some (s.read r)) :
    LeafM.vals (regListM regs) σ M = some fun r => s.read r := by
  simp only [LeafM.vals, regListM, mapM_regs regs s hr, Option.map_some, Option.some.injEq]
  funext r
  have := r.isLt
  simp [List.getD_eq_getElem?_getD, this]

/-- **Soundness of the block executor with loads.** -/
theorem cfgSymM_sound (code : Code) (cuts : List W64)
    (hcode : ∀ p w, code p = some w → fetch M p = some w) (hra : (σ 1#5).toNat % 4 = 0) :
    ∀ (n : Nat) (first : Bool) (pc : W64) (regs : Reg → ME) (T : TreeM) (m : MState) (o : Out),
      cfgSymM code cuts n first pc regs = some T → T.run σ M = some o → m.memory = M →
      m.core.pc = pc → (∀ r, (regs r).eval σ M = some (m.core.read r)) →
      ∃ k m', Silmaril.Machine.Execution.run MState.stepOpt k m = some m' ∧ m'.memory = M ∧
        OutOK σ m' o
  | 0, _, _, _, _, _, _, h, _, _, _, _ => by simp [cfgSymM] at h
  | n + 1, first, pc, regs, T, m, o, h, ho, hM, hpc, hr => by
    simp only [cfgSymM] at h
    split at h
    next hcut =>
      split at h
      next hok =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := abiOKM_spec hok
        simp only [TreeM.run, vals_of regs m.core hr, Option.map_some, Option.some.injEq] at ho
        subst ho
        refine ⟨0, m, rfl, hM, hpc, fun r => rfl, ?_, fun r hrm => ?_⟩
        · have := hr 1#5; rw [h1] at this; simp only [ME.eval] at this
          exact (Option.some.inj this).symm
        · have := hr r; rw [h2 r hrm] at this; simp only [ME.eval] at this
          exact (Option.some.inj this).symm
      next => cases h
    next =>
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hd, h⟩ := Option.bind_eq_some_iff.mp h
    have hf : fetch m.memory m.core.pc = some w := by rw [hM, hpc]; exact hcode _ _ hw
    cases i with
    | compute c =>
      dsimp only at h
      obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
      have hv := symValueM_sound he hpc hr
      let m1 : MState := { m with core := c.step m.core }
      have s1 : m.stepOpt = some m1 := stepOpt_of hf hd rfl
      have hr1 : ∀ r, (updM regs c.dest e r).eval σ M = some (m1.core.read r) :=
        updM_sound hr c.dest e _ hv
      obtain ⟨k, m', hrun, hM', hok⟩ := cfgSymM_sound code cuts hcode hra n false (pc + 4) _ T m1
        o h ho hM (by simp [m1, Compute.step, hpc]) hr1
      exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
    | load op rd rs1 off =>
      cases op with
      | ld =>
        dsimp only at h
        obtain ⟨T', hT', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [TreeM.run] at ho
        obtain ⟨v, hv, ho⟩ := Option.bind_eq_some_iff.mp ho
        have hea : (ME.bin .add (regs rs1) (.const (off.signExtend 64))).eval σ M =
            some (effectiveAddress m.core rs1 off) := by
          simp [ME.eval, Bin.eval, hr, effectiveAddress]
        rw [ME.eval, hea, Option.bind_some, ld64] at hv
        split at hv
        next hal =>
          obtain ⟨bytes, hb, rfl⟩ := Option.map_eq_some_iff.mp hv
          let m1 : MState := { m with core := { m.core.write rd (LoadOp.ld.value bytes) with
            pc := m.core.pc + 4 } }
          have s1 : m.stepOpt = some m1 := by
            refine stepOpt_of hf hd ?_
            exact Instr.exec_load m hal (hM ▸ hb)
          have hr1 : ∀ r, (updM regs rd (.ld (.bin .add (regs rs1) (.const (off.signExtend 64))))
              r).eval σ M = some (m1.core.read r) := by
            refine updM_sound hr rd _ _ ?_
            rw [ME.eval, hea, Option.bind_some, ld64, ite_eq_left hal, hb]; rfl
          obtain ⟨k, m', hrun, hM', hok⟩ := cfgSymM_sound code cuts hcode hra n false (pc + 4)
            _ T' m1 o hT' ho hM (by simp [m1, hpc]) hr1
          exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
        next => cases hv
      | _ => cases h
    | branch op rs1 rs2 half =>
      dsimp only at h
      split at h
      next hal =>
        obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨f, hf', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [TreeM.run, hr, Option.bind_some] at ho
        by_cases hb : op.eval (m.core.read rs1) (m.core.read rs2)
        · rw [ite_eq_left hb] at ho
          let m1 : MState := { m with core := { m.core with pc := pc + branchOffset half } }
          have s1 : m.stepOpt = some m1 := by
            refine stepOpt_of hf hd ?_
            simp only [Instr.exec, hb, ite_true, jumpTo, hpc, hal, m1]
          obtain ⟨k, m', hrun, hM', hok⟩ :=
            cfgSymM_sound code cuts hcode hra n false _ regs t m1 o ht ho hM rfl (fun r => hr r)
          exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
        · rw [ite_eq_right hb] at ho
          let m1 : MState := { m with core := { m.core with pc := pc + 4 } }
          have s1 : m.stepOpt = some m1 := by
            refine stepOpt_of hf hd ?_
            simp only [Instr.exec, hb, Bool.false_eq_true, ite_false, hpc, m1]
          obtain ⟨k, m', hrun, hM', hok⟩ :=
            cfgSymM_sound code cuts hcode hra n false _ regs f m1 o hf' ho hM rfl (fun r => hr r)
          exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
      next => cases h
    | jal rd half =>
      dsimp only at h
      split at h
      next hc =>
        obtain ⟨rfl, hal⟩ := hc
        let m1 : MState := { m with core := { m.core with pc := pc + jalOffset half } }
        have s1 : m.stepOpt = some m1 := by
          refine stepOpt_of hf hd ?_
          simp only [Instr.exec, jumpTo, State.write_zero, hpc, hal, ite_true, m1]
        obtain ⟨k, m', hrun, hM', hok⟩ :=
          cfgSymM_sound code cuts hcode hra n false _ regs T m1 o h ho hM rfl (fun r => hr r)
        exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
      next => cases h
    | jalr rd rs1 off =>
      dsimp only at h
      split at h
      next hc =>
        obtain ⟨rfl, rfl, rfl, hok⟩ := hc
        obtain ⟨h1, h2⟩ := abiOKM_spec hok
        simp only [Option.some.injEq] at h
        subst h
        simp only [TreeM.run, hr, Option.map_some, Option.some.injEq] at ho
        subst ho
        have hra' : m.core.read 1#5 = σ 1#5 := by
          have := hr 1#5; rw [h1] at this; simp only [ME.eval] at this
          exact (Option.some.inj this).symm
        let m1 : MState := { m with core := { m.core with pc := σ 1#5 } }
        have s1 : m.stepOpt = some m1 := by
          refine stepOpt_of hf hd ?_
          have ht : jalrTarget m.core 1#5 0#12 = σ 1#5 := by
            rw [jalrTarget, effectiveAddress, hra']; exact ret_target _ hra
          simp only [Instr.exec, jumpTo, ht, hra, ite_true, State.write_zero, m1]
        refine ⟨1, m1, by simp [Silmaril.Machine.Execution.run, s1], hM, rfl, rfl, ?_⟩
        intro r hrm
        show m.core.read r = σ r
        have := hr r; rw [h2 r hrm] at this; simp only [ME.eval] at this
        exact (Option.some.inj this).symm
      next => cases h
    | store => cases h
    | ebreak => cases h

/-- **A block step with loads**: from `Reach m₀ pc σ`, a defined outcome of the block at `pc`
(all its loads aligned and readable in `m₀`'s memory) is reached. -/
theorem reach_blockM {m₀ : MState} {code : Code} {cuts : List W64} {n : Nat} {pc : W64}
    {σ : Reg → W64} {T : TreeM} {o : Out}
    (hcode : ∀ p w, code p = some w → fetch m₀.memory p = some w)
    (hra : (m₀.core.read 1#5).toNat % 4 = 0)
    (hT : cfgSymM code cuts n true pc regs0M = some T) (h : Reach m₀ pc σ)
    (ho : T.run σ m₀.memory = some o) : BlockOut m₀ o := by
  obtain ⟨k, m, hrun, hM, hpc, hr, h1, hcs⟩ := h
  have hrr : ∀ r, (regs0M r).eval σ m₀.memory = some (m.core.read r) := by
    intro r
    by_cases h0 : r = 0#5
    · subst h0; simp [regs0M, ME.eval]
    · simp [regs0M, h0, ME.eval, hr]
  obtain ⟨k', m', hrun', hM', hok⟩ := cfgSymM_sound (σ := σ) code cuts hcode (h1 ▸ hra) n true pc
    regs0M T m o hT ho hM hpc hrr
  have hrun2 : Silmaril.Machine.Execution.run MState.stepOpt (k + k') m₀ = some m' := by
    rw [run_add, hrun, Option.bind_some, hrun']
  cases o with
  | ret v =>
    obtain ⟨hp, ha, hc⟩ := hok
    exact ⟨_, m', hrun2, by rw [hp, h1], ha, fun r hr' => by rw [hc r hr', hcs r hr']⟩
  | goto pc' σ' =>
    obtain ⟨hp, hr', h1', hc⟩ := hok
    exact ⟨_, m', hrun2, hM', hp, hr', by rw [h1', h1], fun r hr'' => by rw [hc r hr'', hcs r hr'']⟩

end Silmaril.Sim.RV64.CfgM
