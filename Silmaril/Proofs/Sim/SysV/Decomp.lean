module

public import Silmaril.Proofs.Sim.SysV.Sound

/-!
# Decomposing the wrapper's Wasm problem

The Wasm problem of a function called through the wrapper (`WGoal`) splits into the Wasm problem
of the function body alone (`Silmaril.Sim.X86.G.WProblem`: registers in, registers out) and generic
facts about the wrapper, proved once here:

* `step_progress`, **`runExt_progress`**: translated bodies retire from every state whose
  modelled flags are defined (so retirement is not a separate obligation);
* `GRegs.enc`: a store holding registers (and flag bits) encodes some x86 state with defined
  modelled flags;
* `statusOf_self`: unchanged `rsp` and callee-saved registers give status `0`;
* **`wgoal_of_body`**: `WProblem P host code BPre BPost` plus the glue conditions
  (`BPre` holds at the entry registers, `BPost` preserves `rsp` and the callee-saved registers
  and implies `Post` of `rax`) give `WGoal P host code n Pre Post`.
-/

@[expose] public section

namespace Silmaril.Sim.SysV

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.Wasm.Logic.Hoare (HWP)
open Silmaril.X86 (Reg State MState Word)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G

variable {H : Type} {s : Store H} {f : Frame}

/-- The four modelled flags are defined. -/
def FlagsDef (σ : State) : Prop :=
  σ.flags.carry.isSome ∧ σ.flags.zero.isSome ∧ σ.flags.sign.isSome ∧ σ.flags.overflow.isSome

open Silmaril.X86.Ext (writeRM retire aluStep) in
/-- Every instruction of the G fragment retires from a state with defined modelled flags, and
leaves them defined (from `G.progress_defined` and `G.core_shape`). -/
theorem step_progress {i : Silmaril.X86.Ext.Instr} {core : List Instr} (hc : emitCore i = some core)
    (σ : State) (hσ : FlagsDef σ) (m : Memory) (len : Nat) :
    ∃ σ', Silmaril.X86.Ext.exec i σ m len = .ok σ' m ∧ FlagsDef σ' := by
  obtain ⟨σ', hx⟩ := Silmaril.Sim.X86.G.progress_defined hc hσ m len
  exact ⟨σ', hx, (Silmaril.Sim.X86.G.core_shape (H := Nat) (f := {}) hc hx).2.2.2.1 hσ⟩

/-- **Retirement is automatic**: a translated straight-line body retires from every state with
defined modelled flags (memory unchanged). -/
theorem runExt_progress {p : XProg} {code : List Instr} (hc : emitProg p = some code) (σ : State)
    (hσ : FlagsDef σ) (m : Memory) : ∃ σ', runExt p σ m = some (σ', m) := by
  induction p generalizing σ code with
  | nil => exact ⟨σ, rfl⟩
  | cons x p ih =>
    obtain ⟨i, n⟩ := x
    simp only [emitProg, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hc
    obtain ⟨c₁, h₁, cs, h₂, rfl⟩ := hc
    simp only [emit, Option.map_eq_some_iff] at h₁
    obtain ⟨core, hcore, -⟩ := h₁
    obtain ⟨σ₁, hx, hσ₁⟩ := step_progress hcore σ hσ m n
    obtain ⟨σ', h'⟩ := ih h₂ σ₁ hσ₁
    exact ⟨σ', by simp only [runExt, hx]; exact h'⟩

theorem entryCore_flags (d : SysVCall) (σ : State) : (entryCore d σ).flags = σ.flags := by
  suffices ∀ (as : List Word) (rs : List Reg) (τ : State), (setArgs as rs τ).flags = τ.flags by
    exact this _ _ _
  intro as
  induction as with
  | nil => intro rs τ; cases rs <;> rfl
  | cons a as ih => intro rs τ; cases rs with
    | nil => rfl
    | cons r rs => exact (ih rs _).trans rfl

theorem flagsDef_entryCore {d : SysVCall} {σ : State} (h : FlagsDef σ) : FlagsDef (entryCore d σ) := by
  unfold FlagsDef; rw [entryCore_flags]; exact h

/-- A store holding registers and flag bits encodes an x86 state with those registers (and
defined modelled flags). -/
theorem GRegs.enc {R : Reg → Word} (h : GRegs s f R) :
    ∃ σ : State, Enc s f σ ∧ σ.read = R ∧ FlagsDef σ := by
  obtain ⟨hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩ := h
  refine ⟨{ regs := R, rip := w, flags := ⟨some bc, none, none, some bz, some bs, some bo⟩ },
    ⟨hl, hr, hw, ⟨bc, hc, rfl⟩, ⟨bz, hz, rfl⟩, ⟨bs, hs, rfl⟩, ⟨bo, ho, rfl⟩⟩, rfl, by simp [FlagsDef]⟩

theorem nz_zero : nz 0 = 0 := rfl

/-- Unchanged `rsp` and callee-saved registers: status `0`. -/
theorem statusOf_self {e g : Reg → Word}
    (h : g .rsp = e .rsp ∧ g .rbx = e .rbx ∧ g .rbp = e .rbp ∧ g .r12 = e .r12 ∧ g .r13 = e .r13 ∧
      g .r14 = e .r14 ∧ g .r15 = e .r15) : statusOf e g = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [statusOf, h1, h2, h3, h4, h5, h6, h7, BitVec.xor_self]
  rfl

/-- A deterministic evaluation gives every-run correctness. -/
theorem hwp_of_exec {P : Profile} {host : HostSemantics H} {code : List Instr} {s' : Store H}
    {f' : Frame} {rs : List Val} {Q : Silmaril.Wasm.Logic.Core.Post H}
    (he : exec s f [] code = some (s', f', rs)) (hq : Q s' f' (.normal rs.reverse)) :
    HWP P host s f (expression code) Q := by
  have h := Silmaril.Wasm.Examples.Common.Wp.exec_eq (m := .part) (P := P) (host := host)
    (s := s) (f := f) (vs := []) (rest := []) (Q := Q) he
    (by rw [List.append_nil]; exact Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .part) (P := P) (host := host) hq)
  simpa [vals] using h

/-- **The decomposition**: the body's Wasm problem (and its retirement) solves the wrapper's
Wasm problem. -/
theorem wgoal_of_body {P : Profile} {host : HostSemantics H} {p : XProg} {code : List Instr}
    (hc : emitProg p = some code) {n : Nat} {Pre : SysVCall → Prop} {Post : SysVCall → Word → Prop}
    {BPre : (Reg → Word) → Prop} {BPost : (Reg → Word) → (Reg → Word) → Prop}
    (hW : WProblem P host code BPre BPost)
    (hpre : ∀ (d : SysVCall) (σ : State), Pre d → BPre (entryCore d σ).read)
    (hpost : ∀ (d : SysVCall) (σ : State) (R' : Reg → Word), Pre d → BPost (entryCore d σ).read R' →
      (R' .rsp = (entryCore d σ).read .rsp ∧ R' .rbx = (entryCore d σ).read .rbx ∧
        R' .rbp = (entryCore d σ).read .rbp ∧ R' .r12 = (entryCore d σ).read .r12 ∧
        R' .r13 = (entryCore d σ).read .r13 ∧ R' .r14 = (entryCore d σ).read .r14 ∧
        R' .r15 = (entryCore d σ).read .r15) ∧ Post d (R' .rax)) :
    WGoal P host code n Pre Post := by
  intro s f R d hd hn hpre' hG hL
  subst hn
  obtain ⟨σ, hE, -, hσ⟩ := GRegs.enc hG
  obtain ⟨σ', hx⟩ := runExt_progress hc (entryCore d σ) (flagsDef_entryCore hσ) ⟨[], ∅⟩
  obtain ⟨s', f', he, -⟩ := wrapper_exec hc hE hd.1 hL hx
  -- the body's Wasm problem at the entry store
  obtain ⟨s₁, f₁, -, -, hE₁, -, -⟩ := prologue_exec hE hd.1 hL
  obtain ⟨s₂, hE₂, -, -, hb⟩ := hwp_transfer (P := P) (host := host) hc hE₁ hx
    (hW s₁ f₁ _ hE₁.gregs (hpre d σ hpre'))
  obtain ⟨hregs, hp⟩ := hpost d σ σ'.read hpre' (hb σ'.read hE₂.2.1)
  exact hwp_of_exec he ⟨_, _, by simp, statusOf_self hregs, hp⟩

end Silmaril.Sim.SysV
