module

public import Silmaril.Sim.X86.G.Defs

/-!
# Control flow: x86 code with jumps as a Wasm dispatcher loop (header)

* `XTab`: x86 code as a table of decoded instructions at addresses (`(address, instr, length)`);
  `lookupI tab w`: the first instruction at address `w`.
* `XRun tab m k σ σ'`: an `Ext.exec` run of `k` steps from `σ` (memory `m`), each executing the
  instruction at RIP, ending at the first state whose RIP is not in the table (e.g. the `ret`).
* **`dispCode ctab`**: the Wasm dispatcher (P-inline with control flow): a `loop` whose body is,
  for each entry `(a, code)`, `if (rip == a) { code; br 1 }`; when no entry matches, the loop
  falls through. `compileTab tab` fills in the method code (`emitX`, jumps included);
  `Supported tab`: every entry has a method.
* **`LProblem P host code Pre Post`**: the Wasm problem: from every store holding registers `R`
  and RIP `w` with `Pre R w`, every run of `code` that stops falls through with registers `R'`
  satisfying `Post R R'` (partial correctness, `HWP`).
* **`XLProblem tab Pre Post`**: the x86 problem: every `XRun` from a state with `Pre` ends with
  `Post`. `Silmaril.Sim.X86.Loop.xlproblem_of_lproblem` reduces it to `LProblem`.
* `TabAt mem tab`: the memory decodes, at each address of the table, to its instruction.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State)
open Silmaril.Sim.X86.G

/-- x86 code: decoded instructions with lengths at addresses. -/
abbrev XTab := List (Word × Silmaril.X86.Ext.Instr × Nat)

/-- The first instruction at address `w`. -/
def lookupI : XTab → Word → Option (Silmaril.X86.Ext.Instr × Nat)
  | [], _ => none
  | (a, i) :: t, w => if w = a then some i else lookupI t w

/-- The first code at address `w`. -/
def lookupC : List (Word × List Instr) → Word → Option (List Instr)
  | [], _ => none
  | (a, c) :: t, w => if w = a then some c else lookupC t w

/-- A run of `k` instructions of the table from `σ`, ending where RIP leaves the table. -/
inductive XRun (tab : XTab) (m : Silmaril.Process.Memory) : Nat → State → State → Prop
  | done {σ : State} : lookupI tab σ.rip = none → XRun tab m 0 σ σ
  | step {σ σ₁ σ' : State} {i : Silmaril.X86.Ext.Instr} {n k : Nat} :
      lookupI tab σ.rip = some (i, n) → Silmaril.X86.Ext.exec i σ m n = .ok σ₁ m →
      XRun tab m k σ₁ σ' → XRun tab m (k + 1) σ σ'

/-- Every instruction of the table has a method. -/
def Supported (tab : XTab) : Prop := ∀ e ∈ tab, (emitX e.2.1 e.2.2).isSome

/-- The table of method code. -/
def compileTab (tab : XTab) : List (Word × List Instr) :=
  tab.map fun e => (e.1, (emitX e.2.1 e.2.2).getD [])

/-- One dispatcher entry: `if (rip == a) { code; br 1 }` (`br 1` continues the loop). -/
def entryCode (a : Word) (code : List Instr) : List Instr :=
  [gget .rip, c64 a, .intRelOp .i64 .eq, .if_ .empty (code ++ [.br ⟨1⟩]) []]

/-- The dispatcher's loop body. -/
def chainCode : List (Word × List Instr) → List Instr
  | [] => []
  | (a, c) :: t => entryCode a c ++ chainCode t

/-- **The dispatcher**: run the entry at RIP until RIP leaves the table. -/
def dispCode (ctab : List (Word × List Instr)) : List Instr := [.loop .empty (chainCode ctab)]

variable {H : Type}

/-- **The Wasm problem** of a dispatcher. -/
def LProblem (P : Profile) (host : HostSemantics H) (code : List Instr)
    (Pre : (Reg → Word) → Word → Prop)
    (Post : (Reg → Word) → Word → (Reg → Word) → Word → Prop) : Prop :=
  ∀ (s : Store H) (f : Frame) (R : Reg → Word) (w : Word), GRegs s f R →
    gval s f .rip = some (Val.i64 w) → Pre R w →
    Silmaril.Wasm.Logic.Hoare.HWP P host s f (expression code) fun s' f' o => o = .normal [] ∧
      ∀ (R' : Reg → Word) (w' : Word), (∀ r, gval s' f' (.reg r) = some (Val.i64 (R' r))) →
        gval s' f' .rip = some (Val.i64 w') → Post R w R' w'

/-- **The x86 problem** of a table of code. -/
def XLProblem (tab : XTab) (Pre : (Reg → Word) → Word → Prop)
    (Post : (Reg → Word) → Word → (Reg → Word) → Word → Prop) : Prop :=
  ∀ (σ σ' : State) (m : Silmaril.Process.Memory) (k : Nat), Pre σ.read σ.rip →
    XRun tab m k σ σ' → Post σ.read σ.rip σ'.read σ'.rip

/-- The memory decodes, at each address of the table, to its instruction. -/
def TabAt (mem : Silmaril.Process.Memory) (tab : XTab) : Prop :=
  ∀ e ∈ tab, Silmaril.X86.Ext.fetch mem e.1.toNat = .decoded e.2.1 e.2.2

end Silmaril.Sim.X86.Loop
