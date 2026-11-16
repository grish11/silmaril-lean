module

public import Silmaril.Sim.RV64.Mem.Defs

/-!
# Reducing RV64 problems to Wasm problems through the memory-state simulator: definitions

An RV64 problem "from `σ₀`, the program halts after `n` steps in a state satisfying `Φ`"
(`Silmaril.Sim.RV64.Halts`) is posed as a **Wasm problem** about the simulator module `simM`
running the program from its own memory: a chain of `n + 1` Hoare triples for the export `step`
(`StepTriple`), one per retired instruction plus one for the stop, over predicates `I j` on the
memory bytes. Each triple is an ordinary `Silmaril.Wasm.Logic.Hoare.FSpecValid` goal about the
concrete module, solvable by `wpc`/`wat_vc` (symbolic execution of the simulator on the program's
bytes); `Silmaril.Sim.RV64.Reduce.reduce` transports a solution back to the RV64 reference.

* `tripleSpec fi a ma mt Pre Post`: calling `step` (instance `fi` at address `a`, memory `ma` of
  type `mt`) from memory bytes satisfying `Pre` returns one status `st` and bytes `B'` with
  `Post st B'`;
* `WasmRun fi a ma mt I n`: the Wasm problem (`I j → (status 0 ∧ I (j + 1))` for `j < n`, then
  `I n → status ≠ 0`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Reduce

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Words (MemAt)
open Silmaril.Sim.RV64.Mem

variable {H : Type}

/-- A Hoare triple for one call of `step`, over the memory bytes. -/
def tripleSpec (fi : FuncInst H) (a ma : Nat) (mt : MemoryType) (Pre : ByteArray → Prop)
    (Post : BitVec 32 → ByteArray → Prop) : Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ args = [] ∧ ∃ B, MemAt s fi.module ma mt B ∧ Pre B
  post _ _ s' o := ∃ (st : BitVec 32) (B' : ByteArray), o = .normal [.num ⟨.int .i32, st⟩] ∧
    MemAt s' fi.module ma mt B' ∧ Post st B'

/-- **The Wasm problem** for an `n`-instruction run: `n` retiring calls of `step` through the
cut predicates `I 0, …, I n`, then a stopping call. -/
def WasmRun (P : Profile) (host : HostSemantics H) (fi : FuncInst H) (a ma : Nat)
    (mt : MemoryType) (I : Nat → ByteArray → Prop) (n : Nat) : Prop :=
  (∀ j < n, Silmaril.Wasm.Logic.Hoare.FSpecValid P host a
    (tripleSpec fi a ma mt (I j) fun st B' => st = 0 ∧ I (j + 1) B')) ∧
  Silmaril.Wasm.Logic.Hoare.FSpecValid P host a (tripleSpec fi a ma mt (I n) fun st _ => st ≠ 0)

end Silmaril.Sim.RV64.Reduce
