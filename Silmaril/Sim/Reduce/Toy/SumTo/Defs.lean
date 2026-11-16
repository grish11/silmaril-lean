module

public import Silmaril.Sim.X86.SumTo.Defs
public import Silmaril.Sim.Reduce.Toy.Defs
public import Silmaril.Sim.Reduce.Loop.Defs

/-!
# The toy's `sum_to` (a loop), reduced to a Wasm problem: statements

The toy's `sum_to` is the runtime test function (`xor/test/je/add/dec/jne/ret`), the function of
`Silmaril.Sim.X86.SumTo`. Its route through Wasm is the x86 **dispatcher** (P-inline with
control flow: `Silmaril.Sim.X86.Loop.dispCode` over the certified methods `emitX`, jumps included;
the cut-point rule `dispatch_hwp`). The pieces:

* **`PieceStmt`**: the Wasm problem `LProblem` of the dispatcher of `sum_to` placed at every
  `b` (partial correctness, every run): it ends with `rax = 0 + ⋯ + rdi`, `rsp` unchanged, RIP
  at the `ret` (`SumPost`);
* `X86Stmt`: the x86 problem `XLProblem` of the table (`xlproblem_of_lproblem` from the piece);
* **`RankStmt`**: the Wasm **termination piece**: a ranking (`Silmaril.Sim.Reduce.Loop.Ranked`) of
  the dispatcher's entries, holding at every store with RIP at `b`;
* `TermStmt`: termination and frame on the x86 side, *derived* from `RankStmt` by the generic
  `Silmaril.Sim.Reduce.Loop.xrun_of_ranked` (the frame `Fr` is `tabWrites (sumTab b) = [rax, rdi]`).
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Toy.SumTo

open Silmaril.X86 (Reg Word State)
open Silmaril.Sim.X86.Loop Silmaril.Sim.X86.SumTo

/-- `sum_to` at relative offsets (`sumTab b = place b sumRel`). -/
def sumRel : Silmaril.Sim.Reduce.Loop.RTab :=
  [(0, .alu .d .xor (.reg .rax) .rax, 2), (2, .test .q (.reg .rdi) .rdi, 3),
    (5, .jcc8 .e 8, 2), (7, .alu .q .add (.reg .rax) .rdi, 3),
    (10, .incdec .q true (.reg .rdi), 3), (13, .jcc8 .ne 0xf8, 2)]

/-- The flag certificate: offsets where the modelled flags are defined. -/
def sumAnn : List Nat := [2, 5, 7, 10, 13]

/-- The frame of a run: registers other than `rax` and `rdi` unchanged. -/
def Fr (τ τ' : State) : Prop := ∀ r, r ≠ .rax → r ≠ .rdi → τ'.read r = τ.read r

/-- **The Wasm piece** (the x86 dispatcher problem), at every placement. -/
def PieceStmt : Prop :=
  ∀ (b : Word) {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H),
    LProblem (H := H) P host (dispCode (compileTab (sumTab b))) (fun _ w => w = b) SumPost

/-- The x86 problem of the table, at every placement. -/
def X86Stmt : Prop := ∀ b : Word, XLProblem (sumTab b) (fun _ w => w = b) SumPost

/-- **The Wasm termination piece**: a ranking of the dispatcher of `sum_to` at every placement. -/
def RankStmt : Prop :=
  ∀ (b : Word) {H : Type} (f : Silmaril.Wasm.Execution.Core.Frame),
    ∃ J : Nat → Silmaril.Wasm.Execution.Core.Store H → Prop,
      Silmaril.Sim.Reduce.Loop.Ranked (compileTab (sumTab b)) f J ∧
      ∀ s R, Silmaril.Sim.X86.G.GRegs s f R →
        Silmaril.Sim.X86.G.gval s f .rip = some (Silmaril.Wasm.Execution.Core.Val.i64 b) → ∃ k, J k s

/-- Termination and frame of the table run (x86 side; derived from `RankStmt`). -/
def TermStmt : Prop :=
  ∀ (b : Word) (m : Silmaril.Process.Memory) (σ : State), σ.rip = b →
    ∃ k σ', XRun (sumTab b) m k σ σ' ∧ Fr σ σ'

end Silmaril.Sim.Reduce.Toy.SumTo
