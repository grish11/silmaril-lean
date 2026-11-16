module

public import Silmaril.Proofs.Sim.RV64.Example.Fast
public import Silmaril.Sim.RV64.Reduce.Thms

/-!
# An RV64 problem solved as a Wasm problem: assembly and transport

* **`wasm_solution`**: the Wasm problem `WasmRun P host fi a ma mt (progInv x y) 2` is solved for
  every instance of `step`, through the specialised semantics of `step`;
* `sim_*`: facts about the instantiated module (`instantiateOnce?`, kernel `decide`);
* **`prog_spec`**: the RV64 statement, transported back by `Silmaril.Sim.RV64.Reduce.reduce`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Example

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.VC Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem Silmaril.Sim.RV64.Reduce
open Silmaril.Wasm.Logic.Words (MemAt)
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (FSpecValid)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The Wasm problem is solved**, for every instance of `step`: each triple from the
specialised semantics of `step` (`triple_of_stepPost`) and the per-instruction obligations
`post_add`, `post_addi`, `post_stop`. -/
theorem wasm_solution {fi : FuncInst H} {a ma : Nat} {mt : MemoryType}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} (hcode : fi.code = .wasm stepFunc)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0)
    (hrs : rs.length = 1) (x y : BitVec 64) :
    WasmRun P host fi a ma mt (progInv x y) 2 := by
  have hwf : ∀ j B, progInv x y j B → WF B := fun _ _ h => h.1
  refine ⟨fun j hj => ?_, triple_of_stepPost hcode he hps hrs (hwf 2)
    fun B st B' hI h => post_stop x y B st B' hI h⟩
  match j, hj with
  | 0, _ => exact triple_of_stepPost hcode he hps hrs (hwf 0) fun B st B' hI h => post_add x y B st B' hI h
  | 1, _ => exact triple_of_stepPost hcode he hps hrs (hwf 1) fun B st B' hI h => post_addi x y B st B' hI h

/-! ## The instantiated module -/

theorem sim_funcs : ∃ fi : FuncInst Nat, simStore.funcs = [fi] ∧ fi.code = .wasm stepFunc ∧
    FnType.ofDefType? fi.type = some tyStep ∧ fi.module.mems = [0] := by
  have hlen : simStore.funcs.length = 1 := by decide +kernel
  obtain ⟨fi, hf⟩ : ∃ fi, simStore.funcs = [fi] := by
    match h : simStore.funcs, hlen with
    | [fi], _ => exact ⟨fi, rfl⟩
  have hc : simStore.funcs.map FuncInst.code = [.wasm stepFunc] := rfl
  have ht : simStore.funcs.map (fun fi => FnType.ofDefType? fi.type) = [some tyStep] := by
    decide +kernel
  have hmm : simStore.funcs.map (·.module.mems) = [[0]] := by decide +kernel
  rw [hf] at hc ht hmm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht hmm
  exact ⟨fi, hf, hc, ht, hmm⟩

theorem sim_mems : ∃ m : MemInst, simStore.mems = [m] := by
  have hlen : simStore.mems.length = 1 := by decide +kernel
  match h : simStore.mems, hlen with
  | [m], _ => exact ⟨m, rfl⟩

/-! ## The RV64 statement -/

/-- **`add a0, a0, a1; addi a0, a0, 1` computes `a0 + a1 + 1`**: from any RV64 state at
`pc = 0x1000` (with the unobservable `x0` slot zero), the reference machine running `prog` at
`0x1000` halts after exactly two steps, with `a0 = x + y + 1` and `pc = 0x1008`. Solved as the
Wasm problem `wasm_solution` about the simulator module and transported by `reduce`. -/
theorem prog_spec (σ : Silmaril.RiscV.State) (h0 : σ.regs 0#5 = 0) (hpc : σ.pc = 0x1000#64) :
    ∃ t, Halts (codeAt 4096 prog) σ 2 t ∧
      t.read 10#5 = σ.read 10#5 + σ.read 11#5 + 1 ∧ t.pc = 0x1008#64 := by
  obtain ⟨fi, hf, hcode, ht, hmm⟩ := sim_funcs
  obtain ⟨m, hms⟩ := sim_mems
  let B := img σ prog
  let s := simStore.setMem 0 ⟨m.type, B⟩
  have hfs : s.funcs[0]? = some fi := by simp [s, Store.setMem, hf]
  have hm : MemAt s fi.module 0 m.type B := ⟨by simp [hmm], by simp [s, Store.setMem, hms]⟩
  have he : Silmaril.Wasm.Validation.Expand fi.type tyStep.toComp :=
    FnType.expand_of_ofDefType? ht
  have hlay : 4096 + 4 * prog.length ≤ 65536 := by decide
  set x := σ.read 10#5
  set y := σ.read 11#5
  have hσ : absState (img σ prog) = σ := absState_img σ prog h0
  have hc : absCode (img σ prog) = codeAt 4096 prog := absCode_img σ prog hlay
  have hI0 : progInv x y 0 B := by
    refine ⟨by simp [B, img_size], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ld64_img_end]; rfl
    · exact ld32_img σ prog 0 (by decide) hlay
    · exact ld32_img σ prog 1 (by decide) hlay
    · simpa [slotVal, hpc] using ld64_img σ prog 0 (by omega)
    · simpa [slotVal, y, Silmaril.RiscV.State.read] using ld64_img σ prog 11 (by omega)
    · simpa [slotVal, x, Silmaril.RiscV.State.read] using ld64_img σ prog 10 (by omega)
  obtain ⟨B', hI, hH⟩ := reduce (P := Profile.spec) (host := fun _ _ _ _ => False) (fi := fi) (a := 0)
    (ma := 0) (mt := m.type) hcode he rfl rfl (wasm_solution hcode he rfl rfl x y) hfs hm
    (wf_img σ prog) hI0
  have hH' : Halts (codeAt 4096 prog) σ 2 (absState B') := hσ ▸ hc ▸ hH
  refine ⟨absState B', hH', ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, hx⟩ := hI
    simp [Silmaril.RiscV.State.read, absState, hx]
  · obtain ⟨-, -, -, -, hp, -⟩ := hI
    simp [absState, hp]

end Silmaril.Sim.RV64.Example
