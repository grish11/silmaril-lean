module

public import Silmaril.Machine.RiscV.Ext.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Sim.RV64.Sym.Defs

/-!
# RV64 problems of the RV64 reduction plans, transported from their Wasm problems: statements

The RV64 problem of a function of `examples/wasm-sim/rv64/problems/*/reduction.toml`, against
`Silmaril.RiscV.Ext.MState.step` (fetch from process memory, decode, execute): from a state whose
`pc` is the entry and whose executable memory holds the function's words there, with a
four-byte-aligned return address in `ra`, the machine retires to the return address with `a0`
satisfying the plan contract (the `Post` of the Wasm entry `Silmaril.WasmSpec.Rv64*`).

* `CodeAt m base ws`: the words `ws` are fetchable at `base, base + 4, …`;
* `FnISA entry ws params Post`: the problem of a leaf function, with the leaf ABI (`ra`,
  `sp`, `s0`–`s11` preserved).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Transfer

open Silmaril.RiscV.Ext

/-- The words `ws` are fetchable at `base + 4 k`. -/
def CodeAt (m : MState) (base : Nat) (ws : List (BitVec 32)) : Prop :=
  ∀ k (h : k < ws.length), fetch m.memory (BitVec.ofNat 64 (base + 4 * k)) = some ws[k]

/-- **The RV64 problem of a leaf function** (plan contract + ABI): from every state at `entry`
whose executable memory holds the words `ws` there and whose `ra` is four-byte aligned, the
machine retires to `ra`, preserves `sp` and `s0`–`s11`, and `a0` satisfies `Post` of the entry
values of the parameter registers `params`. -/
def FnISA (entry : Nat) (ws : List (BitVec 32)) (params : List Silmaril.Sim.RV64.Sym.Reg)
    (Post : List Silmaril.Sim.RV64.Sym.W64 → Silmaril.Sim.RV64.Sym.W64 → Prop) : Prop :=
  ∀ m : MState, m.core.pc = BitVec.ofNat 64 entry → CodeAt m entry ws →
    (m.core.read 1#5).toNat % 4 = 0 →
    ∃ n m', Silmaril.Machine.Execution.run MState.stepOpt n m = some m' ∧
      m'.core.pc = m.core.read 1#5 ∧
      (∀ r ∈ Silmaril.Sim.RV64.Sym.calleeSaved, m'.core.read r = m.core.read r) ∧
      Post (params.map m.core.read) (m'.core.read 10#5)

/-- `FnISA` with a precondition on the entry values of the parameters. -/
def FnISAP (entry : Nat) (ws : List (BitVec 32)) (params : List Silmaril.Sim.RV64.Sym.Reg)
    (Pre : List Silmaril.Sim.RV64.Sym.W64 → Prop)
    (Post : List Silmaril.Sim.RV64.Sym.W64 → Silmaril.Sim.RV64.Sym.W64 → Prop) : Prop :=
  ∀ m : MState, m.core.pc = BitVec.ofNat 64 entry → CodeAt m entry ws →
    (m.core.read 1#5).toNat % 4 = 0 → Pre (params.map m.core.read) →
    ∃ n m', Silmaril.Machine.Execution.run MState.stepOpt n m = some m' ∧
      m'.core.pc = m.core.read 1#5 ∧
      (∀ r ∈ Silmaril.Sim.RV64.Sym.calleeSaved, m'.core.read r = m.core.read r) ∧
      Post (params.map m.core.read) (m'.core.read 10#5)

end Silmaril.Sim.RV64.Transfer
