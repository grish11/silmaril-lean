module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs

/-! Typed execution and word observations for all total compilation outcomes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF
open Tail.Diamond.MLIR.CF (Widths)
open RVSDG (Tuple)
open RVSDG.NestedTheta
open Blocks (Bank)

structure SourceBudget where
  blocks : Nat

structure CFBudget where
  blocks : Nat

structure ThetaBudget where
  activations : Nat

structure Budgets where
  source : SourceBudget
  cf : CFBudget
  theta : ThetaBudget

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}

/-- The two actual artifacts with a common feedback-limit convention. -/
structure Execution (regs : List (ValueSort Width)) (result : Width) where
  cfTarget : Σ Label : List Width → Type, Cfg TargetOp Label (Widths regs) [result]
  numberedTarget : Σ sigs, Graph (Join.Opcode Op) (dataPorts regs) [] sigs [.value (.data result)]
  cfBudget : Nat → CFBudget

/-- Convert a shared feedback limit to the three execution budgets. -/
def Execution.budgets (execution : Execution regs result) (limit : Nat) : Budgets :=
  ⟨⟨3 * limit + 2⟩, execution.cfBudget limit, ⟨limit⟩⟩

def OriginalTargets.execution (targets : OriginalTargets p) : Execution regs result :=
  ⟨⟨_, targets.cf⟩, ⟨_, targets.numbered⟩, fun limit => ⟨3 * limit + 3⟩⟩

def Outcome.execution : Outcome p → Execution regs result
  | .specialized targets => ⟨⟨_, targets.cf⟩, ⟨_, targets.numbered⟩, fun limit => ⟨2 * limit + 3⟩⟩
  | .twoLive targets | .neitherMarked targets => targets.execution

def Outcome.budgets (outcome : Outcome p) (limit : Nat) : Budgets :=
  outcome.execution.budgets limit

/-- Only the specialization depends on the input facts. -/
def Outcome.Compatible (outcome : Outcome p) (facts : Tuple (Fact Word) (dataPorts regs))
    (input : Bank (regs := regs) model) : Prop :=
  match outcome with
  | .specialized _ => TupleCovers facts input
  | .twoLive _ | .neitherMarked _ => True

/-- Access the actual CF artifact while retaining its label family. -/
def Outcome.cfTarget (outcome : Outcome p) :
    Σ Label : List Width → Type, Cfg TargetOp Label (Widths regs) [result] :=
  outcome.execution.cfTarget

/-- Access the actual numbered artifact while retaining its producer table type. -/
def Outcome.numberedTarget (outcome : Outcome p) :
    Σ sigs, Graph (Join.Opcode Op) (dataPorts regs) [] sigs [.value (.data result)] :=
  outcome.execution.numberedTarget

def runSource (p : Program Op regs (.data result)) (input : Bank (regs := regs) model)
    (budget : SourceBudget) : Option (Word result) :=
  p.source.runFrom model budget.blocks 0 input

def Execution.runCF (execution : Execution regs result) (input : Bank (regs := regs) model)
    (budget : CFBudget) : Option (Word result) :=
  (execution.cfTarget.2.run evalOp budget.blocks (encodeValues input)).map (fun env => env.get .here)

def Outcome.runCF (outcome : Outcome p) (input : Bank (regs := regs) model) (budget : CFBudget) :
    Option (Word result) :=
  outcome.execution.runCF input budget

def Execution.runNumbered (execution : Execution regs result) (input : Bank (regs := regs) model)
    (budget : ThetaBudget) : Option (Word result) :=
  (execution.numberedTarget.2.run (Join.model model) budget.activations input).map (fun values => values.get .head)

def Outcome.runNumbered (outcome : Outcome p) (input : Bank (regs := regs) model) (budget : ThetaBudget) :
    Option (Word result) :=
  outcome.execution.runNumbered input budget

/-- The original source's partial return is witnessed by a finite source run. -/
noncomputable def sourcePart (p : Program Op regs (.data result)) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  ⟨∃ value budget, runSource p input budget = some value, fun h => Classical.choose h⟩

/-- Read the word from an actual pure CF denotation. -/
noncomputable def observeCF {Label : List Width → Type}
    (target : Cfg TargetOp Label (Widths regs) [result]) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  ((SwitchAssert.Cfg.embed target).denotePart evalOp (encodeValues input)).bind fun
    | .returned env => Part.some (env.get .here)
    | .aborted => Part.none

/-- Read the word from a numbered graph in the partial semantics with total primitives. -/
noncomputable def observeNumbered {sigs}
    (target : Graph (Join.Opcode Op) (dataPorts regs) [] sigs [.value (.data result)])
    (input : Bank (regs := regs) model) : Part (Word result) :=
  (Partial.observe (MonadicModel.ofRuntime (Join.model model)) target input).map
    (fun values => values.get .head)

noncomputable def Execution.cfPart (execution : Execution regs result) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  observeCF execution.cfTarget.2 input

noncomputable def Execution.numberedPart (execution : Execution regs result)
    (input : Bank (regs := regs) model) : Part (Word result) :=
  observeNumbered execution.numberedTarget.2 input

noncomputable def Outcome.cfPart (outcome : Outcome p) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  outcome.execution.cfPart input

noncomputable def Outcome.numberedPart (outcome : Outcome p) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  outcome.execution.numberedPart input

/-- The actual execution pair agrees with the source on the selected input. -/
structure Execution.Correct (p : Program Op regs (.data result)) (execution : Execution regs result)
    (input : Bank (regs := regs) model) : Prop where
  bounded (limit : Nat) :
    let budgets := execution.budgets limit
    execution.runCF input budgets.cf = runSource p input budgets.source ∧
      execution.runNumbered input budgets.theta = runSource p input budgets.source
  returns_iff (value : Word result) :
    let native := ∃ budget, runSource p input budget = some value
    ((∃ budget, execution.runCF input budget = some value) ↔ native) ∧
      ((∃ budget, execution.runNumbered input budget = some value) ↔ native)

/-- Both target budgets match the source budget, and finite observations
also match when each runner chooses its own bound. -/
structure Correct (outcome : Outcome p) (input : Bank (regs := regs) model) : Prop where
  bounded (limit : Nat) :
    let budgets := outcome.budgets limit
    outcome.runCF input budgets.cf = runSource p input budgets.source ∧
      outcome.runNumbered input budgets.theta = runSource p input budgets.source
  returns_iff (value : Word result) :
    let native := ∃ budget, runSource p input budget = some value
    ((∃ budget, outcome.runCF input budget = some value) ↔ native) ∧
      ((∃ budget, outcome.runNumbered input budget = some value) ↔ native)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
