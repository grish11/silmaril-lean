module

public import Silmaril.Sim.RV64.Reduce.Defs
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# An RV64 problem solved as a Wasm problem: definitions

The RV64 program `prog` is `add a0, a0, a1; addi a0, a0, 1` at `0x1000`. The RV64 problem: from
any state with `pc = 0x1000`, `a0 = x`, `a1 = y`, the reference machine (`Silmaril.RiscV.decode`/
`step` on the fetched words, `Silmaril.Sim.RV64.refStep`) halts after exactly two steps with
`a0 = x + y + 1`.

The Wasm problem (`Silmaril.Sim.RV64.Reduce.WasmRun`) is three Hoare triples for the export `step`
of the concrete simulator module `simM`, over the cut predicates `progInv x y j` on its memory
bytes (code, `code_end`, `pc`, `a0`, `a1`). `simRun` instantiates `simM` (silmaril-lean
`instantiateOnce?`, no imports).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem

/-- `add a0, a0, a1; addi a0, a0, 1`. -/
def prog : List (BitVec 32) := [0x00b50533#32, 0x00150513#32]

/-- The cut predicate after `j` instructions. -/
def progInv (x y : BitVec 64) (j : Nat) (B : ByteArray) : Prop :=
  65536 ≤ B.size ∧ ld64 B 264 = 4104#64 ∧ ld32 B 4096 = 0x00b50533#32 ∧
    ld32 B 4100 = 0x00150513#32 ∧ ld64 B 0 = BitVec.ofNat 64 (4096 + 4 * j) ∧ ld64 B 88 = y ∧
    ld64 B 80 = (match j with | 0 => x | 1 => x + y | _ => x + y + 1)

/-- The instantiation of `simM` against no imports. -/
def simRun : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? (importStore []) simM []

/-- The instantiated store. -/
def simStore : Store Nat := match simRun with | some (s, _, _) => s | none => {}

/-- The module instance. -/
def simMI : ModuleInst := match simRun with | some (_, f, _) => f.module | none => {}

/-- The type `[] → [i32]` of `step`. -/
def tyStep : FnType := ⟨[], [.num (.int .i32)]⟩

end Silmaril.Sim.RV64.Example
