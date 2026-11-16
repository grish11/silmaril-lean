module

public import Silmaril.Proofs.Sim.RV64.Transfer.Generic
public import Silmaril.WasmSpec.Rv64Clamp.Defs

/-!
# `clamp`: the RV64 problem from its Wasm problem (generic translation validation)

Generated from `examples/wasm-sim/rv64/problems/*/reduction.toml` (entry `0x1127c`). The
symbolic tree `T` is checked against the words by `decide` (`sym`, against the generic, once
proved `extSym_sound`); the body condition `body` by the tactic `rv_tv`; then `isa` transports any
solution of `Silmaril.WasmSpec.Rv64Clamp.Spec` to the RV64 problem `ISA`, and `spec_tv` solves the Wasm problem.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Transfer.Clamp

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym Silmaril.Sim.RV64.Transfer Silmaril.Wasm.Game

/-- The words of the function. -/
def words : List (BitVec 32) := [0x00050693, 0x00c55863, 0x00b55a63, 0x00058513, 0x00008067, 0x00060693, 0xfeb54ae3, 0x00068513, 0x00008067]

/-- The parameter registers. -/
def params : List Reg := [10#5, 11#5, 12#5]

/-- The symbolic tree (output of `extSym`, checked by `sym`). -/
def T : Tree := (Tree.br (BranchOp.ge) (E.var 0x0a#5) (E.var 0x0c#5) (Tree.br (BranchOp.lt) (E.var 0x0a#5) (E.var 0x0b#5) (Tree.ret (E.bin (Bin.add) (E.var 0x0b#5) (E.const 0x0000000000000000#64))) (Tree.ret (E.bin (Bin.add) (E.bin (Bin.add) (E.var 0x0c#5) (E.const 0x0000000000000000#64)) (E.const 0x0000000000000000#64)))) (Tree.br (BranchOp.ge) (E.var 0x0a#5) (E.var 0x0b#5) (Tree.ret (E.bin (Bin.add) (E.bin (Bin.add) (E.var 0x0a#5) (E.const 0x0000000000000000#64)) (E.const 0x0000000000000000#64))) (Tree.ret (E.bin (Bin.add) (E.var 0x0b#5) (E.const 0x0000000000000000#64)))))

set_option maxRecDepth 10000 in
theorem sym : extSym (codeAt 0x1127c words) 10 (BitVec.ofNat 64 0x1127c) regs0 = some T := by
  decide

set_option maxRecDepth 10000 in
theorem loops0 : Silmaril.Wasm.Logic.VC.loops Silmaril.WasmSpec.Rv64Clamp.func.body = 0 := by
  simp [Silmaril.WasmSpec.Rv64Clamp.func, Silmaril.WasmSpec.Rv64Clamp.program, Silmaril.Wasm.Logic.VC.loops, Silmaril.Wasm.Logic.VC.ctl]

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **Translation validation (body)**: the body returns `T.eval σ`. -/
theorem body : BodyTV Silmaril.WasmSpec.Rv64Clamp.func params T := by
  rv_tv [params, T, Silmaril.WasmSpec.Rv64Clamp.func, Silmaril.WasmSpec.Rv64Clamp.program]

/-- The instantiated module. -/
def store : Store Nat := Silmaril.WasmSpec.Rv64Clamp.store

/-- The type of the function. -/
def ty : FnType := ⟨[.num (.int .i64), .num (.int .i64), .num (.int .i64)], [.num (.int .i64)]⟩

theorem funcs : ∃ fi : FuncInst Nat, store.funcs[0]? = some fi ∧ fi.code = .wasm Silmaril.WasmSpec.Rv64Clamp.func ∧
    FnType.ofDefType? fi.type = some ty := by
  have hlen : store.funcs.length = 1 := by decide +kernel
  obtain ⟨fi, hf⟩ : ∃ fi, store.funcs = [fi] := by
    match h : store.funcs, hlen with
    | [fi], _ => exact ⟨fi, rfl⟩
  have hc : store.funcs.map FuncInst.code = [.wasm Silmaril.WasmSpec.Rv64Clamp.func] := rfl
  have ht : store.funcs.map (fun fi => FnType.ofDefType? fi.type) = [some ty] := by
    decide +kernel
  rw [hf] at hc ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht
  exact ⟨fi, by rw [hf]; rfl, hc, ht⟩

/-- The plan contract on the list of entry values. -/
def PostL : List W64 → W64 → Prop
  | [a0, a1, a2], r => Silmaril.WasmSpec.Rv64Clamp.Post a0 a1 a2 r
  | _, _ => False

/-- **The RV64 problem** of `clamp` (contract + leaf ABI). -/
def ISA : Prop := FnISA 0x1127c words params PostL

/-- **The transfer**: every solution of the Wasm problem solves the RV64 problem. -/
theorem isa (hS : Silmaril.WasmSpec.Rv64Clamp.Spec) : ISA := by
  obtain ⟨fi, hf, hcode, ht⟩ := funcs
  have he := FnType.expand_of_ofDefType? ht
  refine fnISA_of_wasm (P := Profile.spec) (host := fun _ _ _ _ => False) sym (by decide) store 0
    (run_of_wp hf hcode he rfl rfl fun σ => ?_)
    (fun σ _ _ _ hs => tv_of_body hf hcode he rfl rfl loops0 body σ hs)
  simpa [params, PostL, store, Silmaril.WasmSpec.Rv64Clamp.func] using hS (σ 10#5) (σ 11#5) (σ 12#5) trivial fi hf Profile.spec (fun _ _ _ _ => False)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedSimpArgs false in
/-- **The Wasm problem solved** through the body condition. -/
theorem spec_tv : Silmaril.WasmSpec.Rv64Clamp.Spec := by
  intro a0 a1 a2 _ f₀ _ P host
  have := wp_of_body (P := P) (host := host) loops0 body (fun r => if r = 10#5 then a0 else if r = 11#5 then a1 else a2) Silmaril.WasmSpec.Rv64Clamp.store f₀.module
    (fun s' r => s' = Silmaril.WasmSpec.Rv64Clamp.store ∧ ∃ r_a0, r = [.i64 r_a0] ∧ Silmaril.WasmSpec.Rv64Clamp.Post a0 a1 a2 r_a0)
    ⟨rfl, _, rfl, by
      simp [T, Tree.eval, E.eval, Bin.eval, BranchOp.eval, Silmaril.WasmSpec.Rv64Clamp.Post, BitVec.slt] <;>
        (try split_ifs) <;> (try simp_all) <;> (try omega) <;>
        (try (apply BitVec.eq_of_toInt_eq; omega))⟩
  simpa [params] using this

/-- **The RV64 problem of `clamp` solved.** -/
theorem isa_solved : ISA := isa spec_tv

end Silmaril.Sim.RV64.Transfer.Clamp
