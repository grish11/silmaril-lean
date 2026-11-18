module

public import Silmaril.Sim.X86.Loop.Defs

/-!
# Termination and frame of dispatcher runs from Wasm rankings: definitions

the x86 dispatcher (`Silmaril.Sim.X86.Loop.dispCode`) poses an x86 table of instructions as a
Wasm problem; `xlproblem_of_lproblem` transfers partial correctness. This module adds what total
correctness of the ISA goal needs, as **Wasm pieces + generic theorems**:

* `Ranked ctab f J`: a **Wasm ranking** of the dispatcher's entries: from every store in `J k`
  with RIP at an entry, the entry's code evaluates (`Silmaril.Wasm.Logic.Core.exec`) to a store in
  `J k'` with `k' < k`. A pure Wasm statement (termination of the dispatcher loop);
* `writesOf i`, `tabWrites tab`: the registers an instruction (a table) may write, a syntactic
  function of the instruction forms.

* `flagsOK rt ann entry`: a **decidable flag dataflow check** over a table at relative offsets
  (`place b rt`): with the certificate `ann` (offsets where the modelled flags are defined), every
  flag reader is annotated, the entry is not, and every annotated successor gets defined flags
  (`flagOut`, `succs`).

`Silmaril.Sim.Reduce.Loop.Thms`: `xrun_of_ranked` (a ranking and the check give an x86 table run,
with every register outside `tabWrites` unchanged), `run_of_xrun`, `bytesAt_of_loaded`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.X86 (Reg Word State)

open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop

/-- The registers an instruction may write (its destination register, if any). -/
def writesOf : Silmaril.X86.Ext.Instr → List Reg
  | .mov _ (.reg d) _ => [d]
  | .movI _ (.reg d) _ => [d]
  | .movabs d _ => [d]
  | .alu _ _ (.reg d) _ => [d]
  | .cmov _ _ d _ => [d]
  | .incdec _ _ (.reg d) => [d]
  | .bswap _ d => [d]
  | .movI32 d _ => [d]
  | _ => []

/-- The registers a table may write. -/
def tabWrites (tab : XTab) : List Reg := tab.flatMap fun e => writesOf e.2.1

/-! ## The flag dataflow check -/

/-- Instructions that read the modelled flags. -/
def readsFlags : Silmaril.X86.Ext.Instr → Bool
  | .jcc8 _ _ => true
  | .cmov _ _ _ _ => true
  | _ => false

/-- Whether the flags are defined after `i`, given whether they were before. -/
def flagOut : Silmaril.X86.Ext.Instr → Bool → Bool
  | .alu .q _ _ _, _ => true
  | .test .q _ _, _ => true
  | .alu .d _ _ _, _ => true
  | .test .d _ _, _ => true
  | _, d => d

/-- Successor offsets. -/
def succs (o : Nat) : Silmaril.X86.Ext.Instr → Nat → List Nat
  | .jcc8 _ rel, n => [o + n, (o + n + (rel.signExtend 64).toNat) % 2 ^ 64]
  | .jmp8 rel, n => [(o + n + (rel.signExtend 64).toNat) % 2 ^ 64]
  | _, n => [o + n]

/-- A table at relative offsets. -/
abbrev RTab := List (Nat × Silmaril.X86.Ext.Instr × Nat)

/-- The table placed at `b`. -/
def place (b : Word) (rt : RTab) : XTab := rt.map fun e => (b + BitVec.ofNat 64 e.1, e.2.1, e.2.2)

/-- **The flag dataflow check**: `ann` lists the offsets where the modelled flags are claimed
defined; the entry is not among them; every flag reader is at an annotated offset; every
successor in `ann` of an instruction gets defined flags from it (`flagOut`); offsets fit. -/
def flagsOK (rt : RTab) (ann : List Nat) (entry : Nat) : Bool :=
  !ann.contains entry && decide (entry < 2 ^ 64) && ann.all (fun o => decide (o < 2 ^ 64)) &&
  rt.all fun e =>
    (!readsFlags e.2.1 || ann.contains e.1) &&
    (succs e.1 e.2.1 e.2.2).all fun o' =>
      decide (o' < 2 ^ 64) && (!ann.contains o' || flagOut e.2.1 (ann.contains e.1))

/-- The flag invariant at a state. -/
def FlagInv (b : Word) (ann : List Nat) (σ : State) : Prop :=
  ∀ o ∈ ann, σ.rip = b + BitVec.ofNat 64 o → Defined σ.flags

variable {H : Type}

/-- **A Wasm ranking of a dispatcher.** -/
def Ranked (ctab : List (Word × List Silmaril.Wasm.Instr)) (f : Frame) (J : Nat → Store H → Prop) :
    Prop :=
  ∀ k s w code, J k s → gval s f .rip = some (Val.i64 w) → lookupC ctab w = some code →
    ∃ s' k', Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) ∧ J k' s' ∧ k' < k

end Silmaril.Sim.Reduce.Loop
