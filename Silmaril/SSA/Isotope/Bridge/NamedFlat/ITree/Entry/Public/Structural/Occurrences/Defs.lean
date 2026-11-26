module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.NamedSSA.Defs

/-! # Typed entry slots for structural capture occurrences -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (Transfer)
open Silmaril.Elgot.ITree (Tree)
open Silmaril.Elgot.ITree.Finite (Event)

namespace StructuralSeed

variable {n : Nat} {V : Type 1}

/-- Give each variable occurrence its own numbered name, in the same order
as the existing footprint and assignment. Units require no slot. -/
def occurrenceOperand (names : Fin n → V) :
    {seed : Val (Fin n)} → {ty : PacketType} → StructuralSeed seed ty → Nat → Val Register
  | _, _, .var _ _, offset => .var ⟨offset⟩
  | _, _, .unit, _ => .unit
  | _, _, .pair left right, offset =>
    .pair (left.occurrenceOperand names offset)
      (right.occurrenceOperand names (offset + (left.footprint names).length))

end StructuralSeed

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType : PacketType} {outputs : Fin exits.length → PacketType}
  (entry : StructuralEntry signature source exits fields inputType outputs)

/-- Slots are distinct names even when they read the same source register. -/
def StructuralEntry.occurrenceNames (i : Fin entry.footprint.length) : Register := ⟨i.val⟩

def StructuralEntry.occurrenceContext : BoundCtx PacketType entry.footprint.length :=
  BoundCtx.ofFin fun i => entry.footprint[i.val].2

def StructuralEntry.occurrenceOperand : Val Register :=
  entry.typedSeed.occurrenceOperand (fun i => entry.names[i.val]) 0

/-- The shared-store decoder supplies one typed packet. Project that packet
to the positional occurrence slots using the existing structural assignment. -/
def StructuralEntry.occurrenceStore (packet : Denote inputType) : Register → Value Atom :=
  fun reg => ((entry.assignment packet)[reg.down]?).elim .unit Prod.snd

/-- Replace the public entry's opaque packet register with the structural
jump through separately typed slots. Private rows and label numbering
come from the already compiled public CFG. -/
def StructuralEntry.occurrenceGraph : CFG Register entry.program.Address F :=
  { entry.program.compile 0 with
    entry := .term (.br ⟨entry.program.entry 0⟩ entry.occurrenceOperand) }

/-- Exact named elaboration and typing of the actual occurrence-entry
graph at the public dispatcher's internal and ordered exit profile. -/
structure OccurrenceAdmission where
  code : FiniteCFG F entry.occurrenceGraph.blocks.length entry.program.exits.length entry.footprint.length
  accepted : NamedFlat.elaborate entry.occurrenceGraph entry.program.exits entry.occurrenceNames = some code
  typed : letI := signature.typing; code.HasType entry.occurrenceContext entry.entry.blocks entry.entry.exits

/-- Check the written adapter through the ordinary exact named typing gate. -/
def StructuralEntry.admitOccurrences : Option (OccurrenceAdmission entry) :=
  letI := signature.typing
  match h : NamedFlat.elaborate entry.occurrenceGraph entry.program.exits entry.occurrenceNames with
  | none => none
  | some code =>
    if ok : NamedFlat.check code entry.occurrenceContext entry.entry.blocks entry.entry.exits = true then
      some ⟨code, h, NamedFlat.check_sound code _ _ _ ok⟩
    else none

/-- The actual named lexical observation, before forgetting entry slots.
The exit numbering and packed output convention are the public runner's. -/
noncomputable def StructuralEntry.observeOccurrences (packet : Denote inputType) :
    Tree (Event signature.Request signature.Reply) (Transfer Atom) :=
  CFG.Cyclic.runSSA (treeModel signature.primitive) entry.occurrenceGraph (entry.occurrenceStore packet) >>=
    fun out => pure (FiniteCFG.packedTreeOutput (treeExitNumber entry.program.exits out))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
