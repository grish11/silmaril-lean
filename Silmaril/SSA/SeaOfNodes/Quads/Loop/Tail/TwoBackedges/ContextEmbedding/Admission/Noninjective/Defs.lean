module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

/-! A write-safe pair of contractions that loses the sole feedback mark at the second cut. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective

open SeaOfNodes.Diamond (dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.Loop.SCCP (bankTuple)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Semantics.Dataflow (Flat)
open RVSDG (Port)
open Composition (thenMap)
open Identification (PortMap Refusal checkWrites program pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width word)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

/-- In order: continuation, selector, seed, multiplier, threshold, and scratch. -/
abbrev old : EntrySignature := { regs := [.predicate, .predicate, word, word, word, word] }

/-- The seed and threshold share their slot. The multiplier remains separate. -/
abbrev middle : EntrySignature := { regs := [.predicate, .predicate, word, word, word] }

/-- The multiplier also shares the seed/threshold slot. -/
abbrev finalSignature : EntrySignature := { regs := [.predicate, .predicate, word, word] }

def seed : Port (dataPorts old.regs) (.value word) := .tail (.tail .head)
def multiplier : Port (dataPorts old.regs) (.value word) := .tail (.tail (.tail .head))
def threshold : Port (dataPorts old.regs) (.value word) := .tail (.tail (.tail (.tail .head)))
def scratch : Port (dataPorts old.regs) (.value word) := .tail (.tail (.tail (.tail (.tail .head))))

def first : PortMap old middle := fun _ => fun
  | .head => .head
  | .tail .head => .tail .head
  | .tail (.tail .head) => .tail (.tail .head)
  | .tail (.tail (.tail .head)) => .tail (.tail (.tail .head))
  | .tail (.tail (.tail (.tail .head))) => .tail (.tail .head)
  | .tail (.tail (.tail (.tail (.tail .head)))) => .tail (.tail (.tail (.tail .head)))

def second : PortMap middle finalSignature := fun _ => fun
  | .head => .head
  | .tail .head => .tail .head
  | .tail (.tail .head) => .tail (.tail .head)
  | .tail (.tail (.tail .head)) => .tail (.tail .head)
  | .tail (.tail (.tail (.tail .head))) => .tail (.tail (.tail .head))

def composed : PortMap old finalSignature := thenMap first second

/-- Seed scratch with 1. Each header scales it and tests the threshold.
Either feedback resets scratch to zero, so an actual run can take one backedge. -/
def body : Program Op old.regs word where
  preheader := [⟨_, _, scratch, .arithmetic (.constant 1), .nil⟩]
  header := [⟨_, _, scratch, .arithmetic (.binary .muli), .cons multiplier (.cons scratch .nil)⟩,
    ⟨_, _, .head, .ult width, .cons threshold (.cons scratch .nil)⟩]
  again := .head
  select := .tail .head
  result := scratch
  feedback _ := [⟨_, _, scratch, .arithmetic (.binary .subi), .cons seed (.cons seed .nil)⟩]

def oldFacts : EntryFacts old.regs :=
  .cons .overdefined (.cons (.constant ⟨true⟩) (.cons (.constant (7 : Word width))
    (.cons .overdefined (.cons .overdefined (.cons .overdefined .nil)))))

def middleFacts : EntryFacts middle.regs :=
  .cons .overdefined (.cons (.constant ⟨true⟩) (.cons (.constant (7 : Word width))
    (.cons .overdefined (.cons .overdefined .nil))))

def finalFacts : EntryFacts finalSignature.regs :=
  .cons .overdefined (.cons (.constant ⟨true⟩) (.cons (.constant (7 : Word width))
    (.cons .overdefined .nil)))

def original : Except SCCP.Dispatch.Refusal (AdmittedAt old width) :=
  @admit _ _ old.bankEq body oldFacts

def writeChecks : Bool × Bool × Bool :=
  (checkWrites first body, checkWrites second (program first body), checkWrites composed body)

/-- Inspect guard operands on the drained FIFO row. The marks list is entry,
true feedback, false feedback, exit, in that order. -/
structure Row where
  scratchAtPhi : Flat (Word width)
  left : Flat (Word width)
  right : Flat (Word width)
  continuation : Flat (ULift Bool)
  marks : List Bool
  deriving DecidableEq, Repr

def row (S : EntrySignature) (map : PortMap old S) (p : Program Op S.regs word)
    (facts : EntryFacts S.regs) : Row :=
  let solved := @SCCP.Worklist.solve _ _ _ _ model p S.bankEq facts
  let phi := bankTuple solved.2.1
  let header := SCCP.blockFacts model p.header phi
  ⟨phi.get (map _ scratch), header.get (map _ threshold), header.get (map _ scratch),
    header.get p.again,
    [decide (SCCP.incomingIndex .entry ∈ solved.1),
      decide (SCCP.incomingIndex (.feedback true) ∈ solved.1),
      decide (SCCP.incomingIndex (.feedback false) ∈ solved.1),
      decide (SCCP.exitIndex ∈ solved.1)]⟩

/-- Execute the actual intersections and FIFO, including the refused final contexts. -/
def rows : Option (List Row) := do
  let mid ← pushFacts first oldFacts
  let via ← pushFacts second mid
  let direct ← pushFacts composed oldFacts
  return [row old (fun _ port => port) body oldFacts,
    row middle first (program first body) mid,
    row finalSignature composed (program second (program first body)) via,
    row finalSignature composed (program composed body) direct]

structure Outcomes where
  first : Except Refusal Bool
  staged : Except LiftComposition.Refused Bool
  direct : Except Refusal Bool
  deriving DecidableEq, Repr

/-- The direct call runs independently of a refusal in the staged call. -/
def outcomes : Option Outcomes := do
  let admitted ← original.toOption
  return ⟨(Identification.compile first admitted).map (fun p => selectedSide p.source),
    (LiftComposition.compare first second admitted).map (fun p => selectedSide p.staged.source),
    (Identification.compile composed admitted).map (fun p => selectedSide p.source)⟩

def input (value : Word width) (side : Bool) : Valuation middle :=
  .cons ⟨false⟩ (.cons ⟨side⟩ (.cons (7 : Word width) (.cons value (.cons (0 : Word width) .nil))))

/-- Run both actual intermediate artifacts with their own evaluator budgets. -/
def runIntermediate (value : Word width) (side : Bool) : Option (Option Nat × Option Nat) := do
  let admitted ← original.toOption
  let artifact ← (Identification.compile first admitted).toOption
  let values := input value side
  return ((artifact.artifacts.cf.run evalOp 12 (encodeValues values)).map (fun env => (env.get .here).toNat),
    (artifact.artifacts.numbered.2.run (Join.model model) 3 values).map
      (fun packet => (packet.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective
