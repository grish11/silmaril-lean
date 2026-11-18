module

public import Silmaril.Proofs.Sim.X86.SumTo.Wasm
public import Silmaril.Sim.X86.Loop.Thms

/-!
# `sum_to`: the x86 problem, solved through Wasm, and the run on the bytes

* `x86_solution`: the x86 problem `XLProblem (sumTab b) …`, by `xlproblem_of_lproblem` from the Wasm
  solution;
* **`sum_returns`**: on the `Silmaril.X86.Ext` machine, from any state whose memory holds the
  bytes `sumBytes` at RIP and the return address `exit` at `[rsp]`, every run that returns to
  `exit` (`Ext.Returns`) returns with `rax = 0 + 1 + ⋯ + rdi` (modulo `2^64`). Partial
  correctness: termination is not claimed.
-/

@[expose] public section

namespace Silmaril.Sim.X86.SumTo

open Silmaril.X86 (Reg Word State MState Byte)
open Silmaril.X86.Ext (Sz RM Cond fetch)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop

theorem supported (b : Word) : Supported (sumTab b) := by
  intro e he
  simp only [sumTab, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The x86 problem of `sum_to`, solved by reduction to the Wasm problem.** -/
theorem x86_solution (b : Word) : XLProblem (sumTab b) (fun _ w => w = b) SumPost :=
  xlproblem_of_lproblem (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False)
    (supported b) (wasm_solution b)

/-- The body and `ret`, decoded, with lengths. -/
def sumProg : XProg :=
  [(.alu .d .xor (.reg .rax) .rax, 2), (.test .q (.reg .rdi) .rdi, 3), (.jcc8 .e 8, 2),
    (.alu .q .add (.reg .rax) .rdi, 3), (.incdec .q true (.reg .rdi), 3), (.jcc8 .ne 0xf8, 2),
    (.ret, 1)]

theorem sumBytes_decode : ∀ (k : Nat) (_h₁ : k < sumProg.length) (h₂ : k < sumBytes.length),
    Silmaril.X86.Ext.decode sumBytes[k] = some sumProg[k] ∧ sumProg[k].2 = sumBytes[k].length := by
  decide +kernel

theorem tabAt {mem : Silmaril.Process.Memory} {b : Word} (h : CodeAt mem b sumProg) :
    TabAt mem (sumTab b) ∧ fetch mem (b + 15).toNat = .decoded .ret 1 := by
  simp only [sumProg, CodeAt, BitVec.add_assoc, BitVec.reduceAdd] at h
  obtain ⟨h0, h2, h5, h7, h10, h13, h15, -⟩ := h
  refine ⟨?_, h15⟩
  intro e he
  simp only [sumTab, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h5
  · exact h7
  · exact h10
  · exact h13

theorem ret_step {exit : Word} {τ : State} {mem : Silmaril.Process.Memory} {stack : List Byte}
    (hf : fetch mem τ.rip.toNat = .decoded .ret 1)
    (hs : mem.readBytes (τ.read .rsp).toNat 8 = some stack)
    (hw : Silmaril.X86.wordOfBytes? stack = some exit) :
    Silmaril.X86.Ext.step exit ⟨τ, mem⟩ =
      .returned ⟨{ τ.write .rsp (τ.read .rsp + 8#64) with rip := exit }, mem⟩ := by
  simp [Silmaril.X86.Ext.step, hf, Silmaril.X86.Ext.exec, Silmaril.X86.popWord, hs, hw]

/-- **`sum_to` on the bytes** (partial correctness). -/
theorem sum_returns {b exit : Word} {σ : State} {mem : Silmaril.Process.Memory}
    (hrip : σ.rip = b) (hb : BytesAt mem b sumBytes) {stack : List Byte}
    (hs : mem.readBytes (σ.read .rsp).toNat 8 = some stack)
    (hw : Silmaril.X86.wordOfBytes? stack = some exit) {final : MState}
    (hR : Silmaril.X86.Ext.Returns exit ⟨σ, mem⟩ final) :
    final.core.rip = exit ∧ final.core.read .rax = BitVec.ofNat 64 (tri (σ.read .rdi).toNat) := by
  obtain ⟨htab, hret⟩ := tabAt (codeAt_of_bytesAt rfl sumBytes_decode hb)
  have hpost : ∀ k τ, XRun (sumTab b) mem k σ τ → SumPost σ.read σ.rip τ.read τ.rip :=
    fun k τ h => x86_solution b σ τ mem k hrip h
  have hstep : ∀ k τ, XRun (sumTab b) mem k σ τ →
      Silmaril.X86.Ext.step exit ⟨τ, mem⟩ =
        .returned ⟨{ τ.write .rsp (τ.read .rsp + 8#64) with rip := exit }, mem⟩ := by
    intro k τ h
    obtain ⟨-, hsp, hr⟩ := hpost k τ h
    exact ret_step (by rw [hr, hrip]; exact hret)
      (by rw [show τ.read .rsp = σ.read .rsp from hsp .rsp (by decide) (by decide)]; exact hs) hw
  obtain ⟨n, ⟨mc, mm⟩, hrun, hfin⟩ := hR
  obtain ⟨k, hk, hmem⟩ : ∃ k, XRun (sumTab b) mem k σ mc ∧ mm = mem :=
    xrun_of_run (supported b) htab n σ ⟨mc, mm⟩ hrun hfin fun k τ h => by
      rw [Silmaril.X86.Ext.stepOpt, hstep k τ h]
  have hfin' : Silmaril.X86.Ext.step exit ⟨mc, mem⟩ = .returned final := hmem ▸ hfin
  have hfinal : final = ⟨{ mc.write .rsp (mc.read .rsp + 8#64) with rip := exit }, mem⟩ :=
    Silmaril.X86.Ext.Outcome.returned.inj (hfin'.symm.trans (hstep k mc hk))
  obtain ⟨hrax, -, -⟩ := hpost k mc hk
  rw [hfinal]
  refine ⟨rfl, ?_⟩
  show (mc.write .rsp (mc.read .rsp + 8#64)).read .rax = _
  rw [State.read_write_other mc .rsp .rax _ (by decide)]
  exact hrax

end Silmaril.Sim.X86.SumTo
