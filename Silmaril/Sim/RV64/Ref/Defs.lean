module

public import Silmaril.Machine.RiscV.Encoding.Defs

/-!
# The RV64 reference machine for the simulators: fetch, decode, execute

The reference semantics against which the Wasm RV64 simulators of `Silmaril.Sim.RV64` are proved
sound: silmaril's RV64 integer fragment (`Silmaril.RiscV`: `Instr`, `decode`, `step`, imported
through the `Silmaril.Machine.RiscV.{Basic,Encoding}` headers), closed under a **code fetch**.

* `Code`: what the machine fetches at a program counter (`none`: fetch fault);
* `codeAt base ws`: the program `ws` (32-bit instruction words) at `base`; fetch is defined
  exactly at the four-byte-aligned addresses `base, base + 4, …` of the words;
* `refStep code s`: fetch at `s.pc`, decode with `Silmaril.RiscV.decode`, retire with
  `Silmaril.RiscV.step`; `none` when the fetch faults or the word is outside the decoder's
  subset (the machine **stops**);
* `refRun code n s`: `n` steps (`none` if it stops earlier); `Halts code s n t`: after `n` steps
  the machine is in `t`, which stops.

The reference model covers exactly the 21 RV64 instructions of `Silmaril.RiscV.Instr`
(ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI, ADD SUB SLL SLT SLTU XOR SRL SRA OR AND, LUI,
AUIPC): no memory access, no control transfer, no traps beyond "stop". A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64

open Silmaril.RiscV

/-- A code fetch: the instruction word at a program counter, `none` for a fetch fault. -/
abbrev Code := Word → Option (BitVec 32)

/-- The program `ws` at `base`: the word `ws[k]` at `base + 4 k`, nothing elsewhere. -/
def codeAt (base : Nat) (ws : List (BitVec 32)) : Code := fun pc =>
  if base ≤ pc.toNat ∧ (pc.toNat - base) % 4 = 0 then ws[(pc.toNat - base) / 4]? else none

/-- **One reference step**: fetch, decode, retire. `none`: the machine stops. -/
def refStep (code : Code) (s : State) : Option State :=
  (code s.pc).bind fun w => (decode w).map fun i => step i s

/-- `n` reference steps. -/
def refRun (code : Code) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (refStep code s).bind (refRun code n)

/-- After `n` steps from `s` the machine is in `t`, and `t` stops. -/
def Halts (code : Code) (s : State) (n : Nat) (t : State) : Prop :=
  refRun code n s = some t ∧ refStep code t = none

end Silmaril.Sim.RV64
