module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

/-! # Three distinct discarded definitions and one retained return word -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example

open SeaOfNodes.Diamond (dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Diamond.MLIR.CF.Example (constant input num regs result selector width zero)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult checkResult)
open Blocks (Bank)
open Blocks.Prune (Mask)

/-- Give the three merge routes distinct definitions of the scratch word.
Block 5 resets that word before either it or the latch can read it. -/
def source : Source Op regs num 7 := fun id =>
  let block := Nested.MLIR.CF.Example.source id
  if id = 2 then {block with body := block.body ++ [constant zero 42]}
  else if id = 3 then {block with body := block.body ++ [constant zero 41]}
  else if id = 4 then {block with body := block.body ++ [constant zero 43]}
  else if id = 5 then {block with body := constant zero 0 :: block.body}
  else block

def plan : Program source 0 := (Nested.check source 0).get (by rfl)

abbrev carry := Nested.MLIR.CF.carriedMask plan
abbrev mask := mergeMask plan

def projected : HeaderProjection (source plan.header).body carry :=
  (Nested.MLIR.CF.prune plan).get (by rfl)

def checked : Checked plan mask := (prune plan).get (by rfl)

def keptResult : KeptResult plan (mask := carry) :=
  (checkResult plan carry).get (by rfl)

def probeBank (value : Word width) : Bank (regs := regs) model :=
  (constant selector value).eval model ((source 0).body.eval model input)

/-- Each row gives predecessor ID, discarded word, and the actual γ's
retained result word for the same selected occurrence. -/
def probe (value : Word width) : Nat × Nat × Option Nat :=
  let old := probeBank value
  let occurrence := plan.selected model old
  let full := plan.mergeBank model old occurrence
  let reduced := (Numbered.mergeRegion plan projected mask).toGraph.run (Join.model model) 0 (carry.project old)
  let port := (mask.rename result).get (by rfl)
  ((plan.predecessor occurrence).val, (full.get zero).toNat, reduced.map (fun bank => (bank.get port).toNat))

def columns : List (Nat × Nat × Option Nat) := [probe 3, probe 2, probe 1]

def runCFEdge (id : Fin 7) (old : Bank (regs := regs) model) :=
  let current := MLIR.CF.siteFrame plan.header plan.join carry mask (out := num) id old
  ((MLIR.CF.lower plan projected checked).block current.label).eval evalOp (fun term env => term.eval env)
    (current.args.append (encodeValues input))

/-- Read the actual γ result signature and one incoming CFG edge's arity. -/
def arities : Nat × Option Nat :=
  let gammaArity := match (Numbered.mergeRegion plan projected mask).toGraph with
    | .region nodes _ _ => (nodes ⟨3, by decide⟩).kind.exit.length
  let direct := runCFEdge 2 ((source 1).body.eval model (probeBank 2))
  let cfArity := match direct with
    | .inl frame => some frame.argsTy.length
    | .inr _ => none
  (gammaArity, cfArity)

def rejects (slot : Nat) : Bool :=
  (checkMask plan (Mask.ofSlots (fun i => i != slot) regs)).isNone

def refusesUsed : Bool × Bool :=
  (rejects result.index, rejects Diamond.MLIR.CF.Example.count.index)

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((MLIR.CF.lower plan projected checked).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

def runRVSDG (fuel : Nat) : Option Nat :=
  ((Numbered.lower plan projected checked keptResult).run (Join.model model) fuel input).map
    (fun values => (values.get .head).toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example
