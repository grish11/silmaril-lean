module

public import Silmaril.Proofs.Sim.X86.Loop.Dispatch
public import Silmaril.Sim.X86.G.Thms

/-!
# The dispatcher's runs on the `Silmaril.X86.Ext` machine

`TabAt mem tab`: the memory decodes, at each address of the table, to its instruction.
**`xrun_of_run`**: a machine run (`Ext.stepOpt exit`) from a state at the table's code, that
cannot retire at any exit of the table (e.g. the exit is a `ret` to `exit`) and ends in a
`returned` step, is an `XRun` of the table: so `XLProblem` facts apply to it.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Loop

open Silmaril.X86 (Reg Word State MState)
open Silmaril.X86.Ext (fetch Fetch)
open Silmaril.Sim.X86.G

theorem lookupI_mem {tab : XTab} {w : Word} {e : Silmaril.X86.Ext.Instr × Nat}
    (h : lookupI tab w = some e) : (w, e) ∈ tab := by
  induction tab with
  | nil => cases h
  | cons x t ih =>
    obtain ⟨a, i⟩ := x
    simp only [lookupI] at h
    split at h
    · rename_i hw; cases h; subst hw; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem emitX_ne_ret {i : Silmaril.X86.Ext.Instr} {n : Nat} (h : (emitX i n).isSome) :
    i ≠ .ret := by
  rintro rfl
  simp [emitX, emit, emitCore] at h

/-- At an address of the table, a step does not return (the table has no `ret`). -/
private theorem step_ne_returned {tab : XTab} (hs : Supported tab)
    {mem : Silmaril.Process.Memory} (hcode : TabAt mem tab) {exit : Word} {σ : State}
    {e : Silmaril.X86.Ext.Instr × Nat} (hl : lookupI tab σ.rip = some e) (final : MState) :
    Silmaril.X86.Ext.step exit ⟨σ, mem⟩ ≠ .returned final := by
  obtain ⟨i, len⟩ := e
  have hf : fetch mem σ.rip.toNat = Fetch.decoded i len := (hcode _ (lookupI_mem hl) :)
  have hnr : i ≠ .ret := emitX_ne_ret (hs _ (lookupI_mem hl))
  intro hret
  simp only [Silmaril.X86.Ext.step, hf] at hret
  split at hret
  · split at hret
    · exact hnr (by tauto)
    · cases hret
  all_goals cases hret

/-- At an address of the table, a step that retires executes the table's instruction there. -/
private theorem exec_of_step_retired {tab : XTab} (hs : Supported tab)
    {mem : Silmaril.Process.Memory} (hcode : TabAt mem tab) {exit : Word} {σ : State}
    {i : Silmaril.X86.Ext.Instr} {len : Nat} (hl : lookupI tab σ.rip = some (i, len))
    {next : MState} (h : Silmaril.X86.Ext.step exit ⟨σ, mem⟩ = .retired next) :
    Silmaril.X86.Ext.exec i σ mem len = .ok next.core next.memory := by
  have hf : fetch mem σ.rip.toNat = Fetch.decoded i len := (hcode _ (lookupI_mem hl) :)
  have hlen : len = i.length := Silmaril.X86.Ext.fetch_length hf
  have hnr : i ≠ .ret := emitX_ne_ret (hs _ (lookupI_mem hl))
  simp only [Silmaril.X86.Ext.step, hf] at h
  split at h
  next core memory hx =>
    split at h
    · exact absurd ‹_ ∧ _›.1 hnr
    · cases h
      rw [hlen]; exact hx
  all_goals cases h

/-- **Machine runs within the table are `XRun`s.** -/
theorem xrun_of_run {tab : XTab} (hs : Supported tab) {mem : Silmaril.Process.Memory}
    (hcode : TabAt mem tab) {exit : Word} {final : MState} :
    ∀ (n : Nat) (σ : State) (mid : MState),
      Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) n ⟨σ, mem⟩ = some mid →
      Silmaril.X86.Ext.step exit mid = .returned final →
      (∀ k τ, XRun tab mem k σ τ → Silmaril.X86.Ext.stepOpt exit ⟨τ, mem⟩ = none) →
      ∃ k, XRun tab mem k σ mid.core ∧ mid.memory = mem := by
  intro n σ mid hrun hret hexit
  induction n generalizing σ mid with
  | zero =>
    show ∃ k, XRun tab mem k σ mid.core ∧ mid.memory = mem
    have hmid : (⟨σ, mem⟩ : MState) = mid := Option.some.inj hrun
    have hdone : lookupI tab σ.rip = none := by
      cases hl : lookupI tab σ.rip with
      | none => rfl
      | some e => exact absurd (by rw [hmid]; exact hret) (step_ne_returned hs hcode hl final)
    rw [← hmid]
    exact ⟨0, .done hdone, rfl⟩
  | succ n ih =>
    show ∃ k, XRun tab mem k σ mid.core ∧ mid.memory = mem
    obtain ⟨⟨core, memory⟩, hs1, hrun'⟩ : ∃ τ₀, Silmaril.X86.Ext.stepOpt exit ⟨σ, mem⟩ = some τ₀ ∧
        Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) n τ₀ = some mid :=
      Option.bind_eq_some_iff.mp hrun
    obtain ⟨⟨i, len⟩, hl⟩ : ∃ e, lookupI tab σ.rip = some e := by
      cases hl : lookupI tab σ.rip with
      | none => exact absurd ((hexit 0 σ (.done hl)).symm.trans hs1) (by simp)
      | some e => exact ⟨e, rfl⟩
    have hx : Silmaril.X86.Ext.exec i σ mem len = .ok core memory :=
      exec_of_step_retired hs hcode hl (Silmaril.X86.Ext.stepOpt_eq_some_iff.mp hs1)
    obtain ⟨code, hcode'⟩ : ∃ code, emitX i len = some code :=
      Option.isSome_iff_exists.mp (hs _ (lookupI_mem hl))
    have hmem : memory = mem := (emitX_shape hcode' hx).1
    have hx' : Silmaril.X86.Ext.exec i σ mem len = .ok core mem := hmem ▸ hx
    have hrun'' : Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) n ⟨core, mem⟩ =
        some mid := hmem ▸ hrun'
    obtain ⟨k, hk, hmid⟩ : ∃ k, XRun tab mem k core mid.core ∧ mid.memory = mem :=
      ih core mid hrun'' hret fun k τ h => hexit (k + 1) τ (.step hl hx' h)
    exact ⟨k + 1, .step hl hx' hk, hmid⟩

end Silmaril.Sim.X86.Loop
