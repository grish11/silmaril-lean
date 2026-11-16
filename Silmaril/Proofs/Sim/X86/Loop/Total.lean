module

public import Silmaril.Proofs.Sim.X86.Loop.Machine
public import Silmaril.Sim.X86.G.Thms

/-!
# The dispatcher: existence of x86 runs (termination) from a measured Wasm invariant

* `emitX_progress`: from a state with defined modelled flags, every instruction with a method
  retires;
* **`xrun_exists`**: a measured invariant `J k` on Wasm stores (the dispatcher's cut-point
  obligations with a decreasing measure, the hypothesis of `dispatch_twp`) and x86 progress on
  states satisfying `D` give an `XRun` from every state encoded by a `J`-store: **termination
  of the x86 code from a Wasm measure**;
* `run_of_xrun`: an `XRun` through code placed in memory is a run of `Ext.stepOpt`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State MState)
open Silmaril.X86.Ext (Cond Result)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec)

variable {H : Type}

/-- Every instruction with a method retires from a state with defined modelled flags. -/
theorem emitX_progress {i : Silmaril.X86.Ext.Instr} {n : Nat} {code : List Instr}
    (hc : emitX i n = some code) {σ : State} (hd : Defined σ.flags)
    (m : Silmaril.Process.Memory) : ∃ σ', Silmaril.X86.Ext.exec i σ m n = .ok σ' m := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, hcc, rfl⟩ | ⟨rel, rfl, rfl⟩ | he
  · obtain ⟨regs, rip, ⟨cf, p, a, z, sg, o⟩, fs⟩ := σ
    obtain ⟨hc', hz', hs', ho'⟩ := hd
    obtain ⟨bc, rfl⟩ := Option.isSome_iff_exists.mp hc'
    obtain ⟨bz, rfl⟩ := Option.isSome_iff_exists.mp hz'
    obtain ⟨bs, rfl⟩ := Option.isSome_iff_exists.mp hs'
    obtain ⟨bo, rfl⟩ := Option.isSome_iff_exists.mp ho'
    cases c <;> simp only [condCode, reduceCtorEq] at hcc <;>
      cases bc <;> cases bz <;> cases bs <;> cases bo <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨core, hcore, -⟩ := Option.map_eq_some_iff.mp he
    exact progress_defined hcore hd m n

/-- **x86 runs exist** (termination) from a measured invariant on Wasm stores. -/
theorem xrun_exists {tab : XTab} (hs : Supported tab) {f : Frame} (J : Nat → Store H → Prop)
    (hstep : ∀ k s, J k s → ∀ w code, gval s f .rip = some (Val.i64 w) →
      lookupC (compileTab tab) w = some code →
      ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, J k' s')
    {m : Silmaril.Process.Memory} (D : State → Prop)
    (hprog : ∀ σ i n, D σ → lookupI tab σ.rip = some (i, n) →
      ∃ σ₁, Silmaril.X86.Ext.exec i σ m n = .ok σ₁ m ∧ D σ₁) :
    ∀ k (s : Store H) σ, J k s → Enc s f σ → D σ → ∃ n σ', XRun tab m n σ σ' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s σ hJ hE hD
  have hl := lookup_compile hs (w := σ.rip)
  cases hi : lookupI tab σ.rip with
  | none => exact ⟨0, σ, .done hi⟩
  | some e =>
    obtain ⟨i, n⟩ := e
    rw [hi] at hl
    obtain ⟨code, hc, hcode⟩ := hl
    obtain ⟨s', he, k', hk', hJ'⟩ := hstep k s hJ σ.rip code hE.2.2.1 hc
    obtain ⟨σ₁, hx, hD₁⟩ := hprog σ i n hD hi
    obtain ⟨-, s₁, he₁, hE₁, -⟩ := emitX_sound hcode hE hx
    rw [he] at he₁
    obtain rfl : s' = s₁ := by simp only [Option.some.injEq, Prod.mk.injEq] at he₁; exact he₁.1
    obtain ⟨n', σ', hr⟩ := ih k' hk' s' σ₁ hJ' hE₁ hD₁
    exact ⟨n' + 1, σ', .step hi hx hr⟩

/-- **An `XRun` through code in memory is a machine run** (retirements only). -/
theorem run_of_xrun {tab : XTab} (hs : Supported tab) {mem : Silmaril.Process.Memory}
    (hcode : TabAt mem tab) (exit : Word) :
    ∀ {k σ σ'}, XRun tab mem k σ σ' →
      Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) k ⟨σ, mem⟩ =
        some ⟨σ', mem⟩
  | _, _, _, .done _ => rfl
  | _, σ, _, .step (i := i) (n := n) (σ₁ := σ₁) hi hx hr => by
    have hm := lookupI_mem hi
    have hf := hcode _ hm
    have hnr := emitX_ne_ret (hs _ hm)
    have hlen := Silmaril.X86.Ext.fetch_length hf
    simp only at hf hlen
    rw [Silmaril.Machine.Execution.run_succ]
    have : Silmaril.X86.Ext.stepOpt exit ⟨σ, mem⟩ = some ⟨σ₁, mem⟩ := by
      rw [Silmaril.X86.Ext.stepOpt_eq_some_iff]
      simp only [Silmaril.X86.Ext.step, hf]
      rw [← hlen, hx]
      simp only at hnr
      simp [hnr]
    rw [this, Option.bind_some]
    exact run_of_xrun hs hcode exit hr

end Silmaril.Sim.X86.Loop
