module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

/-! # Two distinct incoming banks pass through one two-block suffix -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example

open Diamond.MLIR.CF.Example (add input num regs result stride test)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Blocks (Bank)

abbrev original := Nested.MLIR.CF.Example.source

/-- Both inner arms flow through 5 → 6 before entering merge 8.
The outer false arm at 7 enters 8 directly. -/
def source : Source Op regs num 10
  | 0 => ⟨(original 0).body, .transfer (.jump 1)⟩
  | 1 => ⟨(original 1).body, .branch test (.jump 2) (.jump 7)⟩
  | 2 => ⟨(original 2).body, .branch test (.jump 3) (.jump 4)⟩
  | 3 => ⟨[add result result stride], .transfer (.jump 5)⟩
  | 4 => ⟨[add result result result], .transfer (.jump 5)⟩
  | 5 => ⟨[add result result result], .transfer (.jump 6)⟩
  | 6 => ⟨[add result result stride], .transfer (.jump 8)⟩
  | 7 => ⟨(original 4).body, .transfer (.jump 8)⟩
  | 8 => ⟨(original 5).body, .transfer (.jump 9)⟩
  | _ => ⟨(original 6).body, .branch test (.jump 1) (.ret result)⟩

/-- All sites remain reachable, but the outer arm now overlaps the suffix
at its second block. This is outside the checked inner-only overlap. -/
def outerOverlap : Source Op regs num 10 := fun id =>
  if id = 7 then {source id with terminator := .transfer (.jump 6)}
  else source id

def plan : Program source 0 := (Shared.check source 0).get (by rfl)

def columns : List (Nat × Nat) :=
  let first := (source 0).body.eval model input
  [.innerTrue, .innerFalse].map fun occurrence =>
    (((plan.prefixBank model first occurrence).get result).toNat,
      ((plan.mergeBank model first occurrence).get result).toNat)

def nextBank (old : Bank (regs := regs) model) : Bank (regs := regs) model :=
  let incoming := plan.mergeBank model old (plan.toControl.selected model old)
  (source plan.latch).body.eval model ((source plan.join).body.eval model incoming)

def trace : List (Occurrence × Nat × Nat × Nat) :=
  let first := (source 0).body.eval model input
  let second := nextBank first
  let third := nextBank second
  [first, second, third].map fun old =>
    let occurrence := plan.toControl.selected model old
    (occurrence, ((plan.prefixBank model old occurrence).get result).toNat,
      ((plan.mergeBank model old occurrence).get result).toNat, plan.mergeVisits occurrence)

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((lower plan).run evalOp fuel (encodeValues input)).map (fun output => (output.get .here).toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example
