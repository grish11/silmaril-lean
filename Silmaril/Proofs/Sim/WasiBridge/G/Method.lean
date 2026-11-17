module

public import Silmaril.Sim.WasiBridge.G.Defs

/-!
# The `syscall` method and single steps

* `step_progress`: G instructions retire from states with defined modelled flags (`FlagsDef`),
  keeping them defined; `lpsStep_ins`: such a step is a step of LPS's user machine.
* `sysArgs_enc`: the call's arguments are the argument registers.
* **`enc_sysStore`**: the store after the `syscall` method, with the environment's answer `k`
  and `r11 := rflags`, encodes the core LPS resumes with (`sysResume`), whatever the flag
  completion: **the method is sound for the process model's syscall step**.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS.Machines
open Silmaril.Sim.X86.G

variable {H : Type} {s : Store H} {f : Frame}

/-- The four modelled flags are defined. -/
def FlagsDef (σ : State) : Prop :=
  σ.flags.carry.isSome ∧ σ.flags.zero.isSome ∧ σ.flags.sign.isSome ∧ σ.flags.overflow.isSome

theorem step_progress {i : Silmaril.X86.Ext.Instr} {core : List Instr} (hc : emitCore i = some core)
    (σ : State) (hσ : FlagsDef σ) (m : Memory) (len : Nat) :
    ∃ σ', Silmaril.X86.Ext.exec i σ m len = .ok σ' m ∧ FlagsDef σ' := by
  obtain ⟨σ', hx⟩ := progress_defined hc (σ := σ) hσ m len
  exact ⟨σ', hx, (core_shape (H := Nat) (f := {}) hc hx).2.2.2.1 hσ⟩

/-- A G instruction at `rip` is one step of LPS's user machine. -/
theorem lpsStep_ins {i : Silmaril.X86.Ext.Instr} {n : Nat} {code : List Instr} (hc : emit i n = some code)
    {m : MState} (hf : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .decoded i n)
    (hns : ¬ SysAt m.memory m.core.rip) (hσ : FlagsDef m.core) :
    ∃ σ', Silmaril.X86.Ext.exec i m.core m.memory n = .ok σ' m.memory ∧
      lpsStep m = some ⟨σ', m.memory⟩ ∧ FlagsDef σ' ∧ σ'.rip = m.core.rip + BitVec.ofNat 64 n := by
  obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨σ', hx, hσ'⟩ := step_progress hcore m.core hσ m.memory n
  obtain ⟨hrip, hnr, -⟩ := emit_rip hc hx
  have hn : n = i.length := Silmaril.X86.Ext.fetch_length hf
  refine ⟨σ', hx, ?_, hσ', hrip⟩
  have hstep : Silmaril.X86.Ext.stepOpt 0 m = some ⟨σ', m.memory⟩ := by
    rw [Silmaril.X86.Ext.stepOpt_eq_some_iff]
    simp only [Silmaril.X86.Ext.step, hf]
    rw [← hn, hx]
    simp [hnr]
  simp only [lpsStep, SysAt] at hns ⊢
  simp only [hns, ↓reduceIte, hstep]

theorem sysArgs_enc {σ : State} (hE : Enc s f σ) : sysArgs s f = some (sysRegs.map σ.read) := by
  have h := hE.2.1
  simp [sysArgs, sysRegs, h, Val.i64]

/-- Only the modelled flags matter to `Enc`. -/
theorem enc_flags_congr {σ : State} (hE : Enc s f σ) {fl : Silmaril.X86.Flags}
    (hc : fl.carry = σ.flags.carry) (hz : fl.zero = σ.flags.zero) (hs : fl.sign = σ.flags.sign)
    (ho : fl.overflow = σ.flags.overflow) : Enc s f { σ with flags := fl } := by
  obtain ⟨hl, hr, hrip, h1, h2, h3, h4⟩ := hE
  exact ⟨hl, hr, hrip, hc ▸ h1, hz ▸ h2, hs ▸ h3, ho ▸ h4⟩

theorem completeFlag_def {o : Option Bool} (h : o.isSome) (c : Bool) :
    X86FlagChoices.completeFlag o c = o := by
  obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.mp h
  rfl

/-- **The `syscall` method is sound**: after the call answered `v` and `r11` answered with the
completed RFLAGS, the store encodes the core LPS resumes with. -/
theorem enc_sysStore {σ : State} (hE : Enc s f σ) (hσ : FlagsDef σ) (ch : X86FlagChoices.Choice)
    (v : Word) :
    Enc (sysStore s f σ.rip v ((rflagsImage (X86FlagChoices.completeFlags σ.flags ch)).getD 0)) f
      (sysResume σ ch v) := by
  obtain ⟨hc, hz, hs, ho⟩ := hσ
  have h₀ := enc_flags_congr hE (fl := X86FlagChoices.completeFlags σ.flags ch)
    (completeFlag_def hc _) (completeFlag_def hz _) (completeFlag_def hs _) (completeFlag_def ho _)
  let σ₀ : State := { σ with flags := X86FlagChoices.completeFlags σ.flags ch }
  have h₁ := enc_reg h₀ .rax v (σ₀.write .rax v) (regsAfter_write _ _ _ _ rfl) rfl rfl
  have h₂ := enc_reg h₁ .rcx (σ.rip + 2) ((σ₀.write .rax v).write .rcx (σ.rip + 2))
    (regsAfter_write _ _ _ _ rfl) rfl rfl
  have h₃ := enc_reg h₂ .r11 _ (((σ₀.write .rax v).write .rcx (σ.rip + 2)).write .r11
    ((rflagsImage (X86FlagChoices.completeFlags σ.flags ch)).getD 0)) (regsAfter_write _ _ _ _ rfl) rfl rfl
  exact Enc.next h₃ (sysResume σ ch v) rfl rfl _ rfl

theorem flagsDef_sysResume (σ : State) (ch : X86FlagChoices.Choice) (v : Word) :
    FlagsDef (sysResume σ ch v) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Silmaril.Sim.WasiBridge.G
