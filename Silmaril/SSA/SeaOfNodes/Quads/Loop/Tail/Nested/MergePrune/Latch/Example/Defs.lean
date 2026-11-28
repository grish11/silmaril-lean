module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

/-! # Erase merge inputs that are first overwritten in the tested latch -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example

open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Diamond.MLIR.CF.Example
  (add constant count decrement input num regs result selector stride test width zero)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult checkResult)
open Blocks (Bank)
open Blocks.Prune (Mask)

/-- The common merge leaves the distinct incoming `decrement` definitions
alone. The tested latch resets that word before reading it. -/
def source : Source Op regs num 7 := fun id =>
  let block := Nested.MLIR.CF.Example.source id
  if id = 2 then {block with body := block.body ++ [constant decrement 42]}
  else if id = 3 then {block with body := block.body ++ [constant decrement 41]}
  else if id = 4 then {block with body := block.body ++ [constant decrement 43]}
  else if id = 6 then {block with body := constant decrement 255 :: block.body}
  else block

def plan : Program source 0 := (Nested.check source 0).get (by rfl)
abbrev carry := Nested.MLIR.CF.carriedMask plan
abbrev mask := mergeMask plan carry

def projected : HeaderProjection (source plan.header).body carry :=
  (Nested.MLIR.CF.prune plan).get (by rfl)

def checked : Checked plan carry mask := (prune plan carry).get (by rfl)

def keptResult : KeptResult plan (mask := carry) := (checkResult plan carry).get (by rfl)

def probeBank (value : Word width) : Bank (regs := regs) model :=
  (constant selector value).eval model ((source 0).body.eval model input)

/-- Show the predecessor ID, dropped word and the actual γ's retained word. -/
def probe (value : Word width) : Nat × Nat × Option Nat :=
  let old := probeBank value
  let occurrence := plan.selected model old
  let full := plan.mergeBank model old occurrence
  let reduced := (MergePrune.Numbered.mergeRegion plan projected mask).toGraph.run
    (Join.model model) 0 (carry.project old)
  let port := (mask.rename result).get (by rfl)
  ((plan.predecessor occurrence).val, (full.get decrement).toNat, reduced.map (fun bank => (bank.get port).toNat))

def columns : List (Nat × Nat × Option Nat) := [probe 3, probe 2, probe 1]

/-- Inspect the outer γ in the θ body of the emitted loop. -/
def gammaArity : Nat :=
  match (Numbered.thetaBody plan projected checked).toGraph with
  | .region nodes _ _ => (nodes ⟨3, by decide⟩).kind.exit.length

def dropSlot (slot : Nat) : Mask regs := Mask.ofSlots (fun i => i != slot) regs

/-- The same mask dropping only `decrement` passes the packet check and
fails the complete-post-merge-bank check. -/
def overwriteAdmission : Bool × Bool :=
  let reduced := dropSlot decrement.index
  ((checkMask plan carry reduced).isSome, (MergePrune.checkMask plan reduced).isNone)

def tailPacket (old : Bank (regs := regs) model) : Bool × Nat × Nat :=
  let bank := incoming plan mask model old (plan.selected model old)
  let port := (carry.rename decrement).get (by rfl)
  match checked.eval model bank with
  | .cons condition (.cons returned feedback) =>
    (condition.down, returned.toNat, (feedback.get port).toNat)

def tailPackets : List (Bool × Nat × Nat) :=
  let first := (source 0).body.eval model input
  let second := Nested.Numbered.nextBank plan model first
  let third := Nested.Numbered.nextBank plan model second
  [tailPacket first, tailPacket second, tailPacket third]

/-- With no latch write to `test`, its incoming definition is a root,
even though the header projection drops that predicate. -/
def readsIncomingTest : Source Op regs num 7 := fun id =>
  if id = 6 then {source id with body := [constant decrement 255, add count count decrement]}
  else source id

def testPlan : Program readsIncomingTest 0 := (Nested.check readsIncomingTest 0).get (by rfl)

def refusesUsed : Bool × Bool × Bool × Bool :=
  ((checkMask plan carry (dropSlot zero.index)).isNone,
    (checkMask testPlan (Nested.MLIR.CF.carriedMask testPlan) (dropSlot test.index)).isNone,
    (checkMask plan carry (dropSlot stride.index)).isNone,
    (checkMask plan carry (dropSlot count.index)).isNone)

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((Nested.MLIR.CF.lower plan projected).run evalOp fuel (encodeValues input)).map
    (fun env => (env.get .here).toNat)

def runRVSDG (fuel : Nat) : Option Nat :=
  ((Numbered.lower plan projected checked keptResult).run (Join.model model) fuel input).map
    (fun values => (values.get .head).toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example
