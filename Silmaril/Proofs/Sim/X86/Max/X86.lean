module

public import Silmaril.Proofs.Sim.X86.Max.Wasm
public import Silmaril.Sim.X86.G.Thms

/-!
# `max`: the x86 problem, solved through Wasm, and the run on the bytes

* `x86_solution`: the x86 problem of `maxProg`, by `Silmaril.Sim.X86.G.xproblem_of_wproblem` from
  `wasm_solution`. No x86 reasoning beyond the simulator's soundness is used.
* `maxProg_runs`: the body always retires (`cmp` defines the flags `cmovl` reads).
* **`max_returns`**: on the `Silmaril.X86.Ext` machine, from any state whose memory holds the
  bytes `maxBytes` at RIP and the return address `exit` at `[rsp]`, the function returns to
  `exit` (`Ext.Returns`) with `rax` the signed maximum of `rdi` and `rsi`, and every other
  register but `rsp` (popped by `ret`) unchanged.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Max

open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.X86.Ext (Sz RM Cond Result writeRM readRM retire aluStep)
open Silmaril.Sim.X86.G

/-- **The x86 problem of `max`, solved by reduction to the Wasm problem.** -/
theorem x86_solution : XProblem maxProg (fun _ => True) MaxPost :=
  xproblem_of_wproblem (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False) rfl
    wasm_solution

/-- The body of `max` always retires, leaving the memory unchanged. -/
theorem maxProg_runs (σ : State) (mem : Silmaril.Process.Memory) :
    ∃ σ', runExt maxProg σ mem = some (σ', mem) := by
  simp [runExt, maxProg, Silmaril.X86.Ext.exec, writeRM, aluStep, readRM, retire,
    Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.eval_subFlagsN]

theorem maxBytes_decode : ∀ (k : Nat) (_h₁ : k < (maxProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)]).length)
    (h₂ : k < maxBytes.length),
    Silmaril.X86.Ext.decode maxBytes[k] = some (maxProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k] ∧
      (maxProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k].2 = maxBytes[k].length := by
  decide

/-- **`max` on the bytes.** -/
theorem max_returns (m : MState) (exit : Word) (hb : BytesAt m.memory m.core.rip maxBytes)
    {stack : List Byte} (hs : m.memory.readBytes (m.core.read .rsp).toNat 8 = some stack)
    (hw : Silmaril.X86.wordOfBytes? stack = some exit) :
    ∃ final : MState, Silmaril.X86.Ext.Returns exit m final ∧ final.core.rip = exit ∧
      final.core.read .rax =
        (if (m.core.read .rdi).slt (m.core.read .rsi) then m.core.read .rsi else m.core.read .rdi) ∧
      (∀ r, r ≠ .rax → r ≠ .rsp → final.core.read r = m.core.read r) ∧
      final.core.read .rsp = m.core.read .rsp + 8#64 ∧ final.memory = m.memory := by
  obtain ⟨σ, mem⟩ := m
  have hcode := codeAt_of_bytesAt (p := maxProg ++ [(.ret, 1)]) rfl maxBytes_decode hb
  obtain ⟨hbody, hret, -⟩ := codeAt_append hcode
  obtain ⟨σ', hx⟩ := maxProg_runs σ mem
  obtain ⟨hmax, hframe⟩ := x86_solution σ σ' mem mem trivial hx
  obtain ⟨hrun, hrip⟩ := run_of_runExt (code := maxCode) rfl exit hbody hx
  rw [← hrip] at hret
  have hrsp : σ'.read .rsp = σ.read .rsp := hframe .rsp (by decide)
  have hpop : Silmaril.X86.popWord σ' mem = some (exit, σ'.write .rsp (σ'.read .rsp + 8#64)) := by
    simp only [Silmaril.X86.popWord, hrsp]
    simp [hs, hw]
  refine ⟨⟨{ σ'.write .rsp (σ'.read .rsp + 8#64) with rip := exit }, mem⟩,
    ⟨3, ⟨σ', mem⟩, hrun, ?_⟩, rfl, ?_, fun r h₁ h₂ => ?_, ?_, rfl⟩
  · simp only [Silmaril.X86.Ext.step, hret, Silmaril.X86.Ext.exec, hpop]
    simp
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rax = _
    rw [State.read_write_other σ' .rsp .rax _ (by decide)]
    exact hmax
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read r = _
    rw [State.read_write_other σ' .rsp r _ h₂]
    exact hframe r h₁
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]

end Silmaril.Sim.X86.Max
