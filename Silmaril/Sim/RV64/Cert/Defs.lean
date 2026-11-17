module

public import Silmaril.Sim.RV64.Example.Defs
public import Silmaril.Sim.Wasm.Defs

/-!
# The memory-state RV64 simulator as a certified simulator of the `Sim` framework: definitions

The instantiated module `simStore` (`Silmaril.Sim.RV64.Example.simRun`) as a
`Silmaril.Sim.Wasm.ExportSim` with one command (`Unit`: one call of the export `step`, status `0`
accepted), locations `Fin 33` (`x0 … x31`, then `pc`, as in `docs/projects/wasm-sim-abi.md`) and
values `Word`; the reference `refM ws` is `Machine.ofStep` of the RV64 fetch-decode-retire step
`refStep (codeAt 0x1000 ws)`. `certR ws` relates a store to a reference state: memory `0` holds
the program `ws` and the state (up to the unobservable backing slot of `x0`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Cert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Sim Silmaril.Sim.Wasm Silmaril.Sim.RV64 Silmaril.Sim.RV64.Mem Silmaril.Sim.RV64.Example
open Silmaril.RiscV (State Word)

/-- The view of an RV64 state: location `l < 32` is `x_l` (reading `0` for `x0`), `32` is `pc`. -/
def viewRV (σ : State) : PState (Fin 33) Word := fun l =>
  some (if l.val < 32 then σ.read (BitVec.ofNat 5 l.val) else σ.pc)

/-- The reference machine running the program `ws` at `0x1000`. -/
def refM (ws : List (BitVec 32)) : Machine Unit (Fin 33) Word :=
  Machine.ofStep (refStep (codeAt 4096 ws)) viewRV

/-- The view of a store: the abstraction of memory `0`. -/
def getM (s : Store Nat) : PState (Fin 33) Word :=
  match s.mems[0]? with
  | some m => viewRV (absState m.bytes)
  | none => fun _ => none

/-- **The simulator as an `ExportSim`**: export `step` at address `0`, no arguments, status `0`
accepted. -/
def simK (P : Profile) (host : HostSemantics Nat) : ExportSim Unit (Fin 33) Word Nat where
  P := P
  host := host
  get := getM
  addr _ := 0
  args _ := []
  ok _ res := res = [.num ⟨.int .i32, 0#32⟩]

/-- `σ` with the unobservable backing slot of `x0` set to zero. -/
def zero0 (σ : State) : State := { σ with regs := fun r => if r = 0#5 then 0 else σ.regs r }

/-- Store `s` holds the program `ws` and the reference state `σ`. -/
def certR (ws : List (BitVec 32)) (s : Store Nat) (σ : State) : Prop :=
  ∃ (m : MemInst) (B : ByteArray), simStore.mems = [m] ∧ s = simStore.setMem 0 ⟨m.type, B⟩ ∧ WF B ∧ absCode B = codeAt 4096 ws ∧
    absState B = zero0 σ

end Silmaril.Sim.RV64.Cert
