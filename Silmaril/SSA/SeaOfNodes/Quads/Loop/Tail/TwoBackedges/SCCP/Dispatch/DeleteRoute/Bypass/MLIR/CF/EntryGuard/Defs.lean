module

public import Silmaril.SSA.MLIR.CF.EntryBranch.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Coverage.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Defs

/-! Emit a single typed CF graph that checks the SCCP entry facts in its entry block. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (valueBits valueWidth)
open Tail.Diamond.MLIR.CF (Widths entryNames)
open Silmaril.MLIR.Arith (Width Var)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.MLIR.SCF.For (weakenVar)
open RVSDG (Port Tuple)
open Blocks (Bank)

variable {Labels : List Width → Type} {Result : List Width}

/-- Test constant facts using two unsigned comparisons. The accumulator is
an `i1` conjunction, and a bottom fact can branch straight to rejection. -/
def tests (accept reject : Labels []) :
    {regs : List (ValueSort Width)} → {Γ : List Width} →
    Tuple (Fact Word) (dataPorts regs) →
    (∀ {s}, Port (dataPorts regs) (.value s) → Var Γ (valueWidth s)) →
    Var Γ i1 → Block TargetOp Labels Γ Result
  | [], _, .nil, _, ok => .terminator (.condBr ok ⟨accept, .nil⟩ ⟨reject, .nil⟩)
  | slot :: _, _, .cons fact rest, names, ok =>
    match fact with
    | .bottom => .terminator (.br ⟨reject, .nil⟩)
    | .overdefined => tests accept reject rest (fun port => names (.tail port)) ok
    | .constant expected =>
      let w := valueWidth slot
      let actual := names .head
      let compared := [i1, i1, i1, i1, i1, w]
      -- The two inequalities are mutually exclusive. Their i1 sum is disequality.
      .letOp (.original (.constant (valueBits expected))) .nil <|
      .letOp (.ult w) (.cons (.there actual) (.cons .here .nil)) <|
      .letOp (.ult w) (.cons (.there .here) (.cons (.there (.there actual)) .nil)) <|
      .letOp (.addi i1) (.cons .here (.cons (.there .here) .nil)) <|
      .letOp (.original (.constant (BitVec.ofBool true))) .nil <|
      .letOp (.addi i1) (.cons .here (.cons (.there .here) .nil)) <|
      .letOp (.original (.binary i1 .muli)) (.cons .here (.cons (weakenVar ok compared) .nil)) <|
      tests accept reject rest (fun port => .there (weakenVar (names (.tail port)) compared)) .here

/-- Both destinations have empty new argument lists. The encoded source bank
remains in the typed external input of the CFG, in its original slot order. -/
def entry {regs : List (ValueSort Width)} (facts : Tuple (Fact Word) (dataPorts regs))
    (accept reject : Labels []) : Block TargetOp Labels (Widths regs) Result :=
  .letOp (.original (.constant (BitVec.ofBool true))) .nil <|
  tests accept reject facts (fun port => .there ((entryNames regs).get port)) .here

variable {regs : List (ValueSort Width)} {result : Width}

abbrev Arms (regs : List (ValueSort Width)) (result : Width) : Bool → List Width → Type
  | true => Bypass.MLIR.CF.Label regs result
  | false => Tail.Diamond.MLIR.CF.Label regs (.data result) 5

abbrev Target (regs : List (ValueSort Width)) (result : Width) :=
  Cfg TargetOp (Silmaril.MLIR.CF.EntryBranch.Label (Arms regs result)) (Widths regs) [result]

variable {p : Program Op regs (.data result)} {facts : Tuple (Fact Word) (dataPorts regs)}
variable [BankDecidableEq Word (dataPorts regs)]

def arms (checked : Checked model p facts) :
    ∀ side, Cfg TargetOp (Arms regs result side) (Widths regs) [result]
  | true => Bypass.MLIR.CF.lower checked
  | false => TwoBackedges.MLIR.CF.lower p

/-- Retain both emitted fragments and dispatch inside their common typed entry. -/
def lower (checked : Checked model p facts) : Target regs result :=
  Silmaril.MLIR.CF.EntryBranch.link (entry facts (.entry true) (.entry false)) (arms checked)

/-- Run the existing FIFO admission once and emit a guarded specialization.
Both-marked and neither-marked analyses retain the existing refusal reasons. -/
def compile (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    Except Refusal (Target regs result) :=
  (Backends.Worklist.admit model p facts).map lower

/-- The selected arm's matching block budget plus one entry guard visit.
The source budget at the same feedback limit is `3 * limit + 2`. -/
def targetFuel (facts : Tuple (Fact Word) (dataPorts regs)) (input : Bank (regs := regs) model)
    (limit : Nat) : Nat :=
  (if @decide _ (decideTupleCovers facts input) then 2 * limit + 3 else 3 * limit + 3) + 1

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard
