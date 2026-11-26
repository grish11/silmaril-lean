module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example.Defs

/-! # Replay the existing deletion fixture in the emitted numbered θ -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example

open Diamond.MLIR.CF.Example (count input regs)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Latch.MLIR.CF.DeadProducer.Example
  (carry checked cut keptResult plan projected shortened source)
open RVSDG.NestedTheta (Graph Kind Term)
open Join (Opcode)
open Blocks (Bank)

def numbered := lower plan projected cut shortened keptResult

def runNumbered (fuel : Nat) : Option Nat :=
  (numbered.run (Join.model model) fuel input).map (fun values => (values.get .head).toNat)

abbrev FixturePort := RVSDG.PortType (SeaOfNodes.Diamond.ValueSort Width) PEmpty.{1}

/-- Inspect the latch suffix of the actual numbered graph before and after
the deletion. The same header and merge precede its pure producers.
Comparisons are `true` and other pure producers are `false`. -/
def latchTests : List Bool × List Bool :=
  let before := Numbered.lower plan projected checked keptResult
  let skip := (source plan.header).body.producers.length + (source plan.join).body.producers.length
  ((thetaTests before ⟨4, by decide⟩).drop skip, (thetaTests numbered ⟨4, by decide⟩).drop skip)
where
  compares : {ins : List (SeaOfNodes.Diamond.ValueSort Width)} →
      {out : SeaOfNodes.Diamond.ValueSort Width} → Op ins out → Bool
    | _, _, .ult _ | _, _, .slt _ => true
    | _, _, .arithmetic _ => false

  isTest : {ins outs : List FixturePort} → Kind (Opcode Op) ins outs → Option Bool
    | _, _, .base (.simple (.pure opcode)) => some (compares opcode)
    | _, _, _ => none

  pureTests {args outs : List FixturePort} : {past sigs : List (List FixturePort)} →
      Term (Opcode Op) args past sigs outs → List Bool
    | _, _, .ret _ => []
    | _, _, .bind node _ rest => (isTest node.kind).toList ++ pureTests rest

  thetaTests {args outs : List FixturePort} {sigs : List (List FixturePort)}
      : Graph (Opcode Op) args [] sigs outs → Fin sigs.length → List Bool
    | .region nodes children _, site =>
      if h : 0 < (nodes site).kind.arity then pureTests (children site ⟨0, h⟩).toTerm else []

def first : Bank (regs := regs) model := (source 0).body.eval model input
def second : Bank (regs := regs) model := Nested.Numbered.nextBank plan model first
def third : Bank (regs := regs) model := Nested.Numbered.nextBank plan model second

def predecessorOrder : List Nat :=
  [first, second, third].map (fun old => (plan.predecessor (plan.selected model old)).val)

def runBody (old : Bank (regs := regs) model) :=
  (thetaBody plan projected cut shortened).toGraph.run (Join.model model) 0 (carry.project old)

/-- Read the actual θ tag, carried counter and carried result word. -/
def feedback : List (Option (Nat × Nat × Nat)) :=
  let port := (carry.rename count).get (by rfl)
  [first, second, third].map fun old => (runBody old).map fun
    | .cons tag packet => (tag.down.val, (packet.get port).toNat, (packet.get keptResult.val).toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example
