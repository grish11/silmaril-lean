module

public import Silmaril.Sim.RV64.Cert.Defs
public import Silmaril.Sim.RV64.Example.Thms
public import Silmaril.Sim.Wasm.Thms

/-!
# The memory-state RV64 simulator as a certified simulator: proofs

* `read_zero0`, `step_zero0`, `refStep_zero0`: the backing slot of `x0` is unobservable;
* `getM_certR`: the view of a related store is the reference view;
* **`simCert`**: an `ExportSim.Cert` of `simK P host` for `refM ws` (every program of at most
  15360 words), from `step_sound`; **`sim_sound`**: `Silmaril.Sim.Sound` by `Cert.sound`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Cert

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim Silmaril.Sim.Wasm Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem Silmaril.Sim.RV64.Example
open Silmaril.Wasm.Logic.Words (MemAt)
open Silmaril.Wasm.Game (FnType)
open Silmaril.RiscV (State Word)

theorem read_zero0 (σ : State) (r : Silmaril.RiscV.Reg) : (zero0 σ).read r = σ.read r := by
  by_cases h : r = 0#5 <;> simp [State.read, zero0, h]

theorem viewRV_zero0 (σ : State) : viewRV (zero0 σ) = viewRV σ := by
  funext l; simp only [viewRV, read_zero0]; rfl

set_option linter.unusedTactic false in
theorem value_zero0 (i : Silmaril.RiscV.Instr) (σ : State) : i.value (zero0 σ) = i.value σ := by
  have hr : ∀ r, (zero0 σ).read r = σ.read r := read_zero0 σ
  cases i
  all_goals (simp only [Silmaril.RiscV.Instr.value, hr]; try rfl)

theorem step_zero0 (i : Silmaril.RiscV.Instr) (σ : State) :
    Silmaril.RiscV.step i (zero0 σ) = zero0 (Silmaril.RiscV.step i σ) := by
  simp only [Silmaril.RiscV.step, value_zero0]
  simp only [zero0, State.write]
  by_cases hd : i.dest = 0#5
  · simp [hd]
  · simp only [hd, ite_false, State.mk.injEq, and_true]
    funext r
    by_cases hr : r = 0#5 <;> by_cases hrd : r = i.dest <;>
      simp_all [Silmaril.Machine.RegisterFile.write]

theorem refStep_zero0 (code : Code) (σ : State) :
    refStep code (zero0 σ) = (refStep code σ).map zero0 := by
  simp only [refStep, show (zero0 σ).pc = σ.pc from rfl]
  cases code σ.pc with
  | none => rfl
  | some w =>
    simp only [Option.bind_some]
    cases Silmaril.RiscV.decode w <;> simp [step_zero0]

theorem getM_certR {ws : List (BitVec 32)} {s : Store Nat} {σ : State} (h : certR ws s σ) :
    getM s = viewRV σ := by
  obtain ⟨m, B, hm, rfl, -, -, hσ⟩ := h
  simp [getM, Store.setMem, hm, hσ, viewRV_zero0]

theorem sim_mems' : ∃ m : MemInst, simStore.mems = [m] := by
  have hlen : simStore.mems.length = 1 := by decide +kernel
  match h : simStore.mems, hlen with
  | [m], _ => exact ⟨m, rfl⟩

/-- **The certificate.** -/
def simCert (P : Profile) (host : HostSemantics Nat) (ws : List (BitVec 32))
    (hws : 4096 + 4 * ws.length ≤ 65536) : (simK P host).Cert (refM ws) where
  R := certR ws
  view_le h := by
    show getM _ ⊑ viewRV _
    rw [getM_certR h]; exact PState.Le.refl _
  load σ := by
    obtain ⟨m, hm⟩ := sim_mems'
    have h0 : (zero0 σ).regs 0#5 = 0 := by simp [zero0]
    have hR : certR ws (simStore.setMem 0 ⟨m.type, img (zero0 σ) ws⟩) σ :=
      ⟨m, _, hm, rfl, wf_img _ ws, absCode_img _ ws hws, absState_img _ ws h0⟩
    exact ⟨_, hR, getM_certR hR⟩
  method := by
    rintro ⟨⟩ (σ : State) s s' f' res ⟨m, B, hms, rfl, hwf, hc, hσ⟩ hok hs
    obtain ⟨fi, hf, hcode, ht, hmm⟩ := sim_funcs
    have hfs : (simStore.setMem 0 ⟨m.type, B⟩).funcs[0]? = some fi := by
      simp [Store.setMem, hf]
    have hm : MemAt (simStore.setMem 0 ⟨m.type, B⟩) fi.module 0 m.type B :=
      ⟨by simp [hmm], by simp [Store.setMem, hms]⟩
    have hv := Silmaril.Wasm.Logic.Hoare.TFSpecAt.valid
      (step_sound (P := P) (host := host) (a := 0) (ma := 0) (mt := m.type) (B := B) hcode
        (FnType.expand_of_ofDefType? ht) rfl rfl)
    obtain ⟨st, B', ho, rfl, hsp⟩ :=
      Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals hv ⟨hfs, rfl, hm, hwf⟩ hs
    have hres : res = [.num ⟨.int .i32, 0#32⟩] := hok
    subst hres
    simp only [Silmaril.Wasm.Logic.Core.Outcome.normal.injEq, List.cons.injEq, and_true] at ho
    cases ho
    rcases hsp with ⟨-, hstep, hso⟩ | ⟨h23, -, -⟩
    · rw [hc, hσ] at hstep
      rw [refStep_zero0] at hstep
      obtain ⟨σ', h1, h2⟩ := Option.map_eq_some_iff.mp hstep
      refine ⟨σ', h1, m, B', hms, by simp [Store.setMem], wf_of_sameOutside hso hwf,
        (absCode_of_sameOutside hso).trans hc, h2.symm⟩
    · rcases h23 with h | h <;> cases h

/-- **The simulator is sound** for the RV64 reference running any program of at most 15360
words, at every profile and host relation (`Silmaril.Sim.Sound`, the framework of `Silmaril.Sim.Core`). -/
theorem sim_sound (P : Profile) (host : HostSemantics Nat) (ws : List (BitVec 32))
    (hws : 4096 + 4 * ws.length ≤ 65536) :
    Silmaril.Sim.Sound (simK P host).toWasmSim.toMachine (refM ws) :=
  (simCert P host ws hws).sound

end Silmaril.Sim.RV64.Cert
