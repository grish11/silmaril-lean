module

public import Silmaril.Wasm.Examples.FarkasAccept.Defs
public import Silmaril.Wasm.Examples.Farkas.Thms
public import Silmaril.Wasm.Examples.LRAT.Thms
public import Silmaril.Wasm.Acceptor.Code.Thms

@[expose] public section

/-!
# The instantiated Farkas acceptor

Kernel-checked facts (`decide +kernel`) about the instance of `prog` computed by
`Silmaril.Wasm.Verify.instance?` (validation and instantiation against no imports): its exported
functions are `3`, `4` (`cabi_realloc`, `check`); every function's code, module instance and
type are the module's; the module instance resolves globals `0 … 4`, memories `0`, `1` and
functions `0 … 4` to the same addresses; the five globals hold their initial values and the two
memories have the module's types.

From them, the checker's fixture `accX top B₁` (`Silmaril.Wasm.Examples.Farkas.Fix`: the module
instance of the acceptor, the heap pointer `top` after the checker's four globals, the ABI memory
`B₁` after its memory) is `Fix.Ok`, and every store of the acceptor (`AccStore`) holds a
machine state of the checker in it with a one-page memory (`accStore_holds`).

`Instr` has no decidable equality, so code is compared with the acceptor kit's Boolean
equality (`Silmaril.Wasm.Acceptor.fnOk`, read back by `fn_of_fnOk`).

A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Verify Silmaril.Wasm.Game
open Silmaril.Wasm.Examples.Farkas
open Silmaril.Wasm.Examples.FarkasAccept

/-! ## The instance -/

/-- The module instance of its functions. -/
def accMi : ModuleInst := Silmaril.Wasm.Acceptor.miOf accS

/-- The type of the acceptor's two exports. -/
def ty4c : CCompType :=
  .func (Ty.ofList [.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)])
    (Ty.ofList [.num (.int .i32)])

/-- The function types of the checker's functions. -/
def farkasTys : List CCompType :=
  [.func (Ty.ofList [.num (.int .i64), .num (.int .i64)]) (Ty.ofList []),
    .func (Ty.ofList [.num (.int .i32), .num (.int .i64)]) (Ty.ofList []),
    .func (Ty.ofList []) (Ty.ofList [.num (.int .i32)])]

/-- The function types of the module's functions, in order. -/
def accTys : List CCompType := farkasTys ++ [ty4c, ty4c]

/-- Function `j` of the store, of the module and its type agree. -/
abbrev accFnOk : Nat → Bool := Silmaril.Wasm.Acceptor.fnOk accS prog accMi accTys

theorem acc_instance : (instance? prog).isSome = true := by decide +kernel

theorem acc_addrs : accI.addrs = [3, 4] := by decide +kernel

theorem acc_imports : accI.imports = [] := by decide +kernel

theorem acc_fnOk : (List.range 5).all accFnOk = true := by decide +kernel

theorem acc_funcs_length : accS.funcs.length = 5 := by decide +kernel

theorem acc_mi : accMi.globals = List.range 5 ∧ accMi.mems = [0, 1] ∧ accMi.funcs = List.range 5 := by
  decide +kernel

theorem acc_globals : accS.globals = [⟨accG32, Val.i32 0⟩, ⟨accG32, Val.i32 0⟩, ⟨accG64, Val.i64 0⟩,
    ⟨accG64, Val.i64 0⟩, ⟨accG32, Val.i32 (BitVec.ofNat 32 heapBase)⟩] := by decide +kernel

theorem acc_mems : accS.mems.map (·.type) = [farkasMemType, accMt] := by decide +kernel

/-! ## From the facts -/

/-- Function `j` of the instance. -/
theorem acc_fn (j : Nat) (hj : j < 5) : ∃ (fi : FuncInst Nat) (f : Func) (ty : CCompType),
    accS.funcs[j]? = some fi ∧ prog.funcs[j]? = some f ∧ accTys[j]? = some ty ∧
    fi.code = .wasm f ∧ fi.module = accMi ∧ Expand fi.type ty :=
  Silmaril.Wasm.Acceptor.fn_of_fnOk acc_fnOk hj

/-- **The checker's fixture in the acceptor**: the acceptor's module instance, the heap pointer
`top` after the checker's globals and the ABI memory `B₁` after its memory. -/
def accX (top : BitVec 32) (B₁ : ByteArray) : Fix :=
  ⟨accMi, [⟨accG32, Val.i32 top⟩], [⟨accMt, B₁⟩]⟩

theorem accX_ok (top : BitVec 32) (B₁ : ByteArray) : (accX top B₁).Ok :=
  ⟨⟨[4], by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.1]; rfl⟩,
    ⟨[1], by rw [show (accX top B₁).mi = accMi from rfl, acc_mi.2.1]⟩⟩

/-- **Every store of the acceptor holds a checker state** in the fixture, with a one-page
memory. -/
theorem accStore_holds {s : Store Nat} {top : BitVec 32} {B₁ : ByteArray} (h : AccStore s top B₁) :
    ∃ m : Mach, HoldsX (accX top B₁) accS.funcs s m ∧ m.mem.size = 65536 := by
  obtain ⟨bad, hr, y, vb, hg⟩ := h.globals
  obtain ⟨B₀, hB₀, hm⟩ := h.mems
  refine ⟨⟨bad, hr, y, vb, B₀⟩, ⟨s, h.funcs, ?_⟩, hB₀⟩
  obtain ⟨⟩ := s
  simp only at hg hm
  simp only [withMachX, hg, hm]
  rfl

end Silmaril.Proofs.Wasm.Examples.FarkasAccept
