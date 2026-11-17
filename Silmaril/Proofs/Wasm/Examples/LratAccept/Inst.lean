module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Nested
public import Silmaril.Wasm.Acceptor.Code.Thms

@[expose] public section

/-!
# The instantiated acceptor

Kernel-checked facts (`decide +kernel`) about the instance of `prog` computed by
`Silmaril.Wasm.Verify.instance?` (validation and instantiation against no imports): its exported
functions are `10`, `11`, `12` (`cabi_realloc`, `check-stream`, `check-nested`); every function's
code, module instance and type are the module's; the module instance resolves globals `0 … 8`,
memories `0`, `1` and functions `0 … 12` to the same addresses; the nine globals hold their
initial values and the two memories have the module's types. From them, the fixture `accX top B₁`
(the instance's functions, the LRAT state, the heap pointer `top`, the ABI memory `B₁`) holds
the LRAT code (`accX_code`), resolves as `MiOk` says (`accX_mi`) and has the ABI memory and the
heap pointer (`accX_abi`).

`Instr` has no decidable equality, so code is compared with the acceptor kit's Boolean
equality (`Silmaril.Wasm.Acceptor.fnOk`, read back by `fn_of_fnOk`).

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Verify Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.LRAT
open Silmaril.Wasm.Examples.LratAccept

/-! ## The instance -/

/-- The module instance of its functions. -/
def accMi : ModuleInst := Silmaril.Wasm.Acceptor.miOf accS

/-- The type of the acceptor's three exports. -/
def ty4c : CCompType :=
  .func (Ty.ofList [.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)])
    (Ty.ofList [.num (.int .i32)])

/-- The function types of the module's functions, in order. -/
def accTys : List CCompType := lratTys ++ [ty4c, ty4c, ty4c]

/-- Function `j` of the store, of the module and its type agree. -/
abbrev accFnOk : Nat → Bool := Silmaril.Wasm.Acceptor.fnOk accS prog accMi accTys

theorem acc_instance : (instance? prog).isSome = true := by decide +kernel

theorem acc_addrs : accI.addrs = [10, 11, 12] := by decide +kernel

theorem acc_imports : accI.imports = [] := by decide +kernel

theorem acc_fnOk : (List.range 13).all accFnOk = true := by decide +kernel

theorem acc_funcs_length : accS.funcs.length = 13 := by decide +kernel

theorem acc_mi : accMi.globals = List.range 9 ∧ accMi.mems = [0, 1] ∧ accMi.funcs = List.range 13 := by
  decide +kernel

theorem acc_globals : accS.globals = (G₀ ++ [16]).map fun v => ⟨accGt, Val.i32 v⟩ := by decide +kernel

theorem acc_mems : accS.mems.map (·.type) = [lratMemType, accMt] := by decide +kernel

/-! ## From the facts -/

/-- Function `j` of the instance. -/
theorem acc_fn (j : Nat) (hj : j < 13) : ∃ (fi : FuncInst Nat) (f : Func) (ty : CCompType),
    accS.funcs[j]? = some fi ∧ prog.funcs[j]? = some f ∧ accTys[j]? = some ty ∧
    fi.code = .wasm f ∧ fi.module = accMi ∧ Expand fi.type ty :=
  Silmaril.Wasm.Acceptor.fn_of_fnOk acc_fnOk hj

/-- The acceptor's fixture: the instance's functions and module instance, the heap pointer `top`
and the ABI memory `B₁` after the LRAT state. -/
def accX (top : BitVec 32) (B₁ : ByteArray) : Fix Nat :=
  ⟨accS.funcs, accMi, accGt, lratMemType, [⟨accGt, Val.i32 top⟩], [⟨accMt, B₁⟩]⟩

theorem accX_mi (top : BitVec 32) (B₁ : ByteArray) : MiOk (accX top B₁) :=
  ⟨fun k hk => by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.1, List.getElem?_range (by omega)],
    by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.1]; rfl⟩

theorem lratModule_funcs (j : Nat) (hj : j < 10) : prog.funcs[j]? = lratModule.funcs[j]? := by
  have hl : lratModule.funcs.length = 10 := rfl
  simp only [prog]
  rw [List.getElem?_append_left (by omega)]

theorem accTys_lt (j : Nat) (hj : j < 10) : accTys[j]? = lratTys[j]? := by
  have hl : lratTys.length = 10 := rfl
  simp only [accTys]
  rw [List.getElem?_append_left (by omega)]

theorem accX_code (top : BitVec 32) (B₁ : ByteArray) : CodeOk (accX top B₁) where
  fn j hj := by
    obtain ⟨fi, f, ty, h1, h2, h3, h4, h5, h6⟩ := acc_fn j (by omega)
    exact ⟨fi, f, ty, h1, by rw [← lratModule_funcs j hj]; exact h2,
      by rw [← accTys_lt j hj]; exact h3, h4, h5, h6⟩
  addr j hj := by
    rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.2, List.getElem?_range (by omega)]

theorem accX_abi (top : BitVec 32) {B₁ : ByteArray} (hsz : B₁.size < 2 ^ 32) : Abi (accX top B₁) B₁ where
  mem1 := by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.1]; rfl
  mrest := ⟨accMt, rfl⟩
  glob8 := by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.1]; rfl
  grest := ⟨_, rfl⟩
  size := hsz

end Silmaril.Proofs.Wasm.Examples.LratAccept
