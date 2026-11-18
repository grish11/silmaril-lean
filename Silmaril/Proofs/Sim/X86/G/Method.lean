module

public import Silmaril.Proofs.Sim.X86.G.Prog

/-!
# The G simulator: the exported methods as Wasm functions

* `core_sound`: the method body alone (`emitCore`, RIP not advanced) is sound;
* `emitCore_progress`: from a state whose modelled flags are all defined (as the state a store
  holds, `stateOf`), every supported instruction retires;
* **`method_valid`**: every function instance whose code is the method of instruction `i`
  meets `methodSpec`, at every profile and for every host relation: from any store holding
  registers, flag bits and RIP in the instance's globals, every call returns (no trap, no
  stuck state), and the result store encodes `Ext.exec i σ` (RIP excepted) for **every** state
  `σ` the initial store encodes and on which `i` retires; only modelled globals change.
* `simModule_*`: the methods of the quoted `simModule` are `emitCore` of their instructions.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec_append exec_nil Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP FSpec FSpecValid)
open Silmaril.X86 (Reg State Flags)
open Silmaril.X86.Ext (Sz RM Cond Result writeRM readRM retire aluStep)

variable {H : Type} {s : Store H} {f : Frame} {σ : State}

/-- **Soundness of a method body** (without the RIP update). -/
theorem core_sound {i : Silmaril.X86.Ext.Instr} {len : Nat} {core : List Instr}
    (hc : emitCore i = some core) (hE : Enc s f σ) {σ' : State} {m m' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    m' = m ∧ CoreOk s f core { σ' with rip := σ.rip } := by
  obtain ⟨hm, -, -, -, hok⟩ := core_shape hc hx
  exact ⟨hm, hok s hE⟩

theorem enc_stateOf {R : Reg → BitVec 64} {w : BitVec 64} {bc bz bs bo : Bool} (hl : Layout s f)
    (hr : ∀ r, gval s f (.reg r) = some (Val.i64 (R r))) (hw : gval s f .rip = some (Val.i64 w))
    (hc : gval s f .cf = some (Val.i64 (b64 bc))) (hz : gval s f .zf = some (Val.i64 (b64 bz)))
    (hs : gval s f .sf = some (Val.i64 (b64 bs))) (ho : gval s f .of = some (Val.i64 (b64 bo))) :
    Enc s f (stateOf R w bc bz bs bo) :=
  ⟨hl, hr, hw, ⟨bc, hc, rfl⟩, ⟨bz, hz, rfl⟩, ⟨bs, hs, rfl⟩, ⟨bo, ho, rfl⟩⟩

/-- `cmov` retires from a state with defined modelled flags. -/
theorem progress_cmov {cnd : Cond} {cc : List Instr} {d src : Reg} (hcc : condCode cnd = some cc)
    {σ : State} (hd : Defined σ.flags) (m : Silmaril.Process.Memory) (len : Nat) :
    ∃ σ', Silmaril.X86.Ext.exec (.cmov .q cnd d (.reg src)) σ m len = .ok σ' m := by
  obtain ⟨regs, rip, ⟨c, p, a, z, sg, o⟩, fs⟩ := σ
  obtain ⟨hc', hz', hs', ho'⟩ := hd
  obtain ⟨bc, rfl⟩ := Option.isSome_iff_exists.mp hc'
  obtain ⟨bz, rfl⟩ := Option.isSome_iff_exists.mp hz'
  obtain ⟨bs, rfl⟩ := Option.isSome_iff_exists.mp hs'
  obtain ⟨bo, rfl⟩ := Option.isSome_iff_exists.mp ho'
  cases cnd <;> simp only [condCode, reduceCtorEq] at hcc <;>
    cases bc <;> cases bz <;> cases bs <;> cases bo <;> exact ⟨_, rfl⟩

/-- Every supported instruction retires from a state with defined modelled flags. -/
theorem progress_defined {i : Silmaril.X86.Ext.Instr} {core : List Instr}
    (hc : emitCore i = some core) {σ : State} (hd : Defined σ.flags)
    (m : Silmaril.Process.Memory) (len : Nat) :
    ∃ σ', Silmaril.X86.Ext.exec i σ m len = .ok σ' m := by
  rcases emitCore_cases hc with
    ⟨_, _, hi, -⟩ | ⟨_, _, hi, -⟩ | ⟨_, _, hi, -⟩ | ⟨op, _, _, hi, -⟩ |
    ⟨_, _, _, _, hi, hcc, -⟩ | ⟨_, _, hi, -⟩ | ⟨_, hi, -⟩ | ⟨_, hi, -⟩ |
    ⟨_, _, hi, -⟩ | ⟨_, hi, -⟩ | ⟨op, _, _, hi, -⟩ | ⟨_, _, hi, -⟩ |
    ⟨_, _, hi, -⟩
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · cases op <;> exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ progress_cmov hcc hd m len
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · cases op <;> exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩
  · exact hi ▸ ⟨_, rfl⟩

/-- Every supported instruction retires from a state with defined modelled flags (the state a
store holds, `stateOf`). -/
theorem emitCore_progress {i : Silmaril.X86.Ext.Instr} {core : List Instr}
    (hc : emitCore i = some core) (R : Reg → BitVec 64) (w : BitVec 64) (bc bz bs bo : Bool)
    (m : Silmaril.Process.Memory) (len : Nat) :
    ∃ σ', Silmaril.X86.Ext.exec i (stateOf R w bc bz bs bo) m len = .ok σ' m :=
  progress_defined hc ⟨rfl, rfl, rfl, rfl⟩ m len

/-! ## Method specifications -/

variable {P : Profile} {host : HostSemantics H}

/-- **Every method meets its specification**, at every profile and for every host relation. -/
theorem method_valid {a : Nat} {fi : FuncInst H} {func : Func} {i : Silmaril.X86.Ext.Instr}
    {ps rs : Validation.Ty (.list .val)} (hcode : fi.code = .wasm func)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0) (hrs : rs.length = 0)
    (hloc : func.locals = []) (hbody : emitCore i = some func.body) :
    FSpecValid P host a (methodSpec fi a i) := by
  refine Silmaril.Wasm.Examples.Common.FSpecValid.of_body_hwp (fun _ _ h => h.1) hcode he
    (fun _ _ h => by rw [h.2.1, hps]; rfl) fun s args h => ?_
  obtain ⟨-, rfl, R, hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩ := h
  rw [hloc]
  have hE := enc_stateOf hl hr hw hc hz hs ho
  obtain ⟨σ₀', hx₀⟩ := emitCore_progress hbody R w bc bz bs bo ⟨[], {}⟩ 0
  obtain ⟨-, s₁, he, hE₁, hF⟩ := core_sound hbody hE hx₀
  have h := Silmaril.Wasm.Examples.Common.Wp.exec_eq (m := .part) (P := P) (host := host)
    (vs := []) (rest := []) he (Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := .part) (P := P)
      (host := host) (vs := [])
      (Q := Silmaril.Wasm.Examples.Common.bodyPost rs.length ((methodSpec fi a i).post s []))
      ⟨by rw [hrs]; rfl, rfl, hF, fun σ σ' m m' len hEσ hx => ?_⟩)
  · simpa [vals] using h
  · obtain ⟨-, s₂, he₂, hE₂, -⟩ := core_sound hbody hEσ hx
    rw [he] at he₂
    obtain rfl : s₁ = s₂ := by simp only [Option.some.injEq, Prod.mk.injEq] at he₂; exact he₂.1
    exact hE₂

/-! ## The quoted module -/

theorem simModule_mov : some simModule.funcs[0].body = emitCore (.mov .q (.reg .rax) .rdi) := rfl
theorem simModule_add : some simModule.funcs[1].body = emitCore (.alu .q .add (.reg .rax) .rsi) :=
  rfl
theorem simModule_sub : some simModule.funcs[2].body = emitCore (.alu .q .sub (.reg .rax) .rsi) :=
  rfl
theorem simModule_xor : some simModule.funcs[3].body = emitCore (.alu .q .xor (.reg .rax) .rsi) :=
  rfl
theorem simModule_cmp : some simModule.funcs[4].body = emitCore (.alu .q .cmp (.reg .rax) .rsi) :=
  rfl
theorem simModule_cmovl :
    some simModule.funcs[5].body = emitCore (.cmov .q .l .rax (.reg .rsi)) := rfl
theorem simModule_locals :
    (simModule.funcs.take 6).map (·.locals) = [[], [], [], [], [], []] := rfl

end Silmaril.Sim.X86.G
