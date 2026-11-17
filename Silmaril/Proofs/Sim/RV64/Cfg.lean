module

public import Silmaril.Sim.RV64.Cfg.Defs
public import Silmaril.Sim.RV64.Sym.Thms

/-!
# Cut points: the block executor is sound

* `cfgSym_sound`: a symbolic block is followed by every concrete run (one proof, by induction on
  the fuel, as `Silmaril.Sim.RV64.Sym.extSym_sound`, plus cut-point leaves and `jal x0`);
* **`reach_block`**: from a state reached at a cut point (`Reach`), a block's outcome is reached:
  the next cut point (`Reach`) or the return (`Returns`); `reach_entry`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Cfg

open Silmaril.RiscV.Ext
open Silmaril.RiscV (State)
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym

/-- What a block's outcome says of the final state, for block-entry values `σ`. -/
def OutOK (σ : Reg → W64) (m' : MState) : Out → Prop
  | .ret v => m'.core.pc = σ 1#5 ∧ m'.core.read 10#5 = v ∧ ∀ r ∈ calleeSaved, m'.core.read r = σ r
  | .goto pc σ' => m'.core.pc = pc ∧ (∀ r, m'.core.read r = σ' r) ∧ σ' 1#5 = σ 1#5 ∧
      ∀ r ∈ calleeSaved, σ' r = σ r

theorem regList_getD (regs : Reg → E) (r : Reg) :
    (regList regs).getD r.toNat (.var r) = regs r := by
  have := r.isLt
  simp [regList, List.getD_eq_getElem?_getD, this]

theorem abiOK_spec {regs : Reg → E} (h : abiOK regs = true) :
    regs 1#5 = .var 1#5 ∧ ∀ r ∈ calleeSaved, regs r = .var r := by
  simp only [abiOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun r hr => by simpa using h.2 r hr⟩

/-- **Soundness of the block executor.** -/
theorem cfgSym_sound (code : Code) (cuts : List W64) (M : Silmaril.Process.Memory)
    (hcode : ∀ p w, code p = some w → fetch M p = some w) (σ : Reg → W64)
    (hra : (σ 1#5).toNat % 4 = 0) :
    ∀ (n : Nat) (first : Bool) (pc : W64) (regs : Reg → E) (T : Tree2) (m : MState),
      cfgSym code cuts n first pc regs = some T → m.memory = M → m.core.pc = pc →
      (∀ r, m.core.read r = (regs r).eval σ) →
      ∃ k m', Silmaril.Machine.Execution.run MState.stepOpt k m = some m' ∧ m'.memory = M ∧
        OutOK σ m' (T.run σ)
  | 0, _, _, _, _, _, h, _, _, _ => by simp [cfgSym] at h
  | n + 1, first, pc, regs, T, m, h, hM, hpc, hr => by
    simp only [cfgSym] at h
    split at h
    next hcut =>
      split at h
      next hok =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := abiOK_spec hok
        refine ⟨0, m, rfl, hM, hpc, fun r => ?_, ?_, fun r hrm => ?_⟩
        · simp only [Leaf.vals, regList_getD, hr]
        · simp only [Leaf.vals, regList_getD, h1, E.eval]
        · simp only [Leaf.vals, regList_getD, h2 r hrm, E.eval]
      next => cases h
    next =>
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
      obtain ⟨k, m', hrun, hM', hok⟩ := cfgSym_sound code cuts M hcode σ hra n false (pc + 4) _ T m1
        h hM (by simp [m1, Compute.step, hpc]) hr1
      exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
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
          obtain ⟨k, m', hrun, hM', hok⟩ :=
            cfgSym_sound code cuts M hcode σ hra n false _ regs t m1 ht hM rfl (fun r => hr r)
          refine ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', ?_⟩
          simpa [Tree2.run, hb] using hok
        · let m1 : MState := { m with core := { m.core with pc := pc + 4 } }
          have s1 : m.stepOpt = some m1 := by
            refine stepOpt_of hf hd ?_
            simp only [Instr.exec, hc, hb, Bool.false_eq_true, ite_false, hpc, m1]
          obtain ⟨k, m', hrun, hM', hok⟩ :=
            cfgSym_sound code cuts M hcode σ hra n false _ regs f m1 hf' hM rfl (fun r => hr r)
          refine ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', ?_⟩
          simpa [Tree2.run, hb] using hok
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
          cfgSym_sound code cuts M hcode σ hra n false _ regs T m1 h hM rfl (fun r => hr r)
        exact ⟨k + 1, m', by simp [Silmaril.Machine.Execution.run, s1, hrun], hM', hok⟩
      next => cases h
    | jalr rd rs1 off =>
      dsimp only at h
      split at h
      next hc =>
        obtain ⟨rfl, rfl, rfl, hok⟩ := hc
        obtain ⟨h1, h2⟩ := abiOK_spec hok
        simp only [Option.some.injEq] at h
        subst h
        have hra' : m.core.read 1#5 = σ 1#5 := by rw [hr, h1]; rfl
        let m1 : MState := { m with core := { m.core with pc := σ 1#5 } }
        have s1 : m.stepOpt = some m1 := by
          refine stepOpt_of hf hd ?_
          have ht : jalrTarget m.core 1#5 0#12 = σ 1#5 := by
            rw [jalrTarget, effectiveAddress, hra']; exact ret_target _ hra
          simp only [Instr.exec, jumpTo, ht, hra, ite_true, State.write_zero, m1]
        refine ⟨1, m1, by simp [Silmaril.Machine.Execution.run, s1], hM, rfl, ?_, ?_⟩
        · show m.core.read 10#5 = _
          rw [hr]
        · intro r hrm
          show m.core.read r = σ r
          rw [hr, h2 r hrm]; rfl
      next => cases h
    | load => cases h
    | store => cases h
    | ebreak => cases h

theorem run_add (a b : Nat) (m : MState) :
    Silmaril.Machine.Execution.run MState.stepOpt (a + b) m =
      (Silmaril.Machine.Execution.run MState.stepOpt a m).bind
        (Silmaril.Machine.Execution.run MState.stepOpt b) := by
  induction a generalizing m with
  | zero => simp [Silmaril.Machine.Execution.run]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [Silmaril.Machine.Execution.run]
    cases m.stepOpt <;> simp [ih]

/-- The entry state is reached at its `pc`. -/
theorem reach_entry (m₀ : MState) : Reach m₀ m₀.core.pc fun r => m₀.core.read r :=
  ⟨0, m₀, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ _ => rfl⟩

/-- The block's outcome from a reached cut point. -/
def BlockOut (m₀ : MState) : Out → Prop
  | .ret v => Returns m₀ v
  | .goto pc σ' => Reach m₀ pc σ'

/-- **A block step**: from `Reach m₀ pc σ`, the outcome of the block at `pc` is reached. -/
theorem reach_block {m₀ : MState} {code : Code} {cuts : List W64} {n : Nat} {pc : W64}
    {σ : Reg → W64} {T : Tree2} (hcode : ∀ p w, code p = some w → fetch m₀.memory p = some w)
    (hra : (m₀.core.read 1#5).toNat % 4 = 0)
    (hT : cfgSym code cuts n true pc regs0 = some T) (h : Reach m₀ pc σ) :
    BlockOut m₀ (T.run σ) := by
  obtain ⟨k, m, hrun, hM, hpc, hr, h1, hcs⟩ := h
  have hrr : ∀ r, m.core.read r = (regs0 r).eval σ := by
    intro r
    by_cases h0 : r = 0#5
    · subst h0; simp [regs0, E.eval]
    · simp [regs0, h0, E.eval, hr]
  obtain ⟨k', m', hrun', hM', hok⟩ := cfgSym_sound code cuts m₀.memory hcode σ (h1 ▸ hra) n true pc
    regs0 T m hT hM hpc hrr
  have hrun2 : Silmaril.Machine.Execution.run MState.stepOpt (k + k') m₀ = some m' := by
    rw [run_add, hrun, Option.bind_some, hrun']
  cases ho : T.run σ with
  | ret v =>
    rw [ho] at hok
    obtain ⟨hp, ha, hc⟩ := hok
    exact ⟨_, m', hrun2, by rw [hp, h1], ha, fun r hr' => by rw [hc r hr', hcs r hr']⟩
  | goto pc' σ' =>
    rw [ho] at hok
    obtain ⟨hp, hr', h1', hc⟩ := hok
    exact ⟨_, m', hrun2, hM', hp, hr', by rw [h1', h1], fun r hr'' => by rw [hc r hr'', hcs r hr'']⟩

end Silmaril.Sim.RV64.Cfg
