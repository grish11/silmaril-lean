module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Defs

/-! # Schedule a direct transfer operand at an original block -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block

open LambdaSSA (FiniteCFG Flat Region)
open Morphism.CaseSSA (erase)
open Silmaril.SSA.LambdaRTL (Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature)

variable {F : Type} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- A direct transfer scheduled in the scope of its incoming packet.
The two equations retain the written operand and the exact outlined tree. -/
structure ScheduledTransfer (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (input : PacketType) (written : Region F) where
  boundary : Boundary sig (.snoc .nil input) (SSA.FiniteSum.append packets outputs)
  source_eq : written = boundary.written
  count : Nat
  tree : EntryTree sig packets outputs [input] count
  tree_eq : boundary.lower = tree.written

/-- Check the operand at an original destination's type, using only
the incoming packet's slots. -/
def readJump [DecidableEq F] (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (input : PacketType) (label : Fin (blocks + exits))
    (original : LambdaSSA.Tm F) : Option (ScheduledTransfer sig packets outputs input (.br label.val original)) := do
  let ⟨arg, exactArg⟩ ← readArgument sig [input] (SSA.FiniteSum.append packets outputs label) original
  let boundary : Boundary sig (.snoc .nil input) (SSA.FiniteSum.append packets outputs) := .jump label arg
  let ⟨count, tree⟩ ← Multiple.read sig packets outputs [input] boundary.lower
  let exact ← commonRow (blocks + exits) boundary.lower tree.written
  return ⟨boundary, congrArg (Region.br label.val) exactArg, count, tree,
    exact.property.1.trans exact.property.2.symm⟩

def readTransfer [DecidableEq F] (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (input : PacketType) {n : Nat} :
    (row : Flat F (blocks + exits) n) → Option (ScheduledTransfer sig packets outputs input row.erase)
  | .br label original => readJump sig packets outputs input label (erase original)
  | _ => none

/-- The selected row uses only its incoming packet. Captures used in the
row must already be carried in that packet. The written entry still
supplies the original seed. -/
structure Shape (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (source : FiniteCFG F blocks exits captures) where
  start : Fin blocks
  seed : Val (Fin captures)
  entry_eq : source.entry.erase = .br start.val (packetTerm seed)
  selected : Fin blocks
  boundary : Boundary sig (.snoc .nil (packets selected)) (SSA.FiniteSum.append packets outputs)
  source_eq : (source.block selected).erase = boundary.written
  count : Nat
  tree : EntryTree sig packets outputs [packets selected] count
  tree_eq : boundary.lower = tree.written

def read [DecidableEq F] (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (source : FiniteCFG F blocks exits captures)
    (selected : Fin blocks) : Option (Shape sig packets outputs source) := do
  let ⟨⟨start, seed⟩, entryEq⟩ ← readEntry source
  let row ← readTransfer sig packets outputs (packets selected) (source.block selected)
  return ⟨start, seed, entryEq, selected, row.boundary, row.source_eq, row.count, row.tree, row.tree_eq⟩

/-- Keep the selected block's original packet type and index. Only its
body changes. Fresh labels extend the table after all old blocks. -/
def Shape.table (s : Shape sig packets outputs source) : Fin (blocks + s.count) → PacketType × Region F :=
  appendTable
    (fun i => (packets i, if i = s.selected then s.tree.entry (oldLabel s.count) (freshLabel blocks)
      else (source.block i).erase.renameLabels (moveExit blocks s.count)))
    (s.tree.cells (oldLabel s.count) (freshLabel blocks))

structure Emitted (s : Shape sig packets outputs source) where
  code : FiniteCFG F (blocks + s.count) exits captures
  entry_eq : code.entry.erase = source.entry.erase
  row_eq : ∀ i, (code.block i).erase = (s.table i).2

def emit (s : Shape sig packets outputs source) : Option (Emitted s) := do
  let labels := blocks + s.count + exits
  let entry ← scopedRow labels captures source.entry.erase
  let rows ← tabulateDependent (blocks + s.count) fun i => scopedRow labels (captures + 1) (s.table i).2
  return ⟨⟨entry.val, fun i => (rows i).val⟩, entry.property, fun i => (rows i).property⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  shape : Shape sig packets outputs source
  emitted : Emitted shape
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  emittedTyped : letI := sig.typing; emitted.code.HasType context (fun i => (shape.table i).1) outputs
  publicReadback : Constructed sig (fun i => (shape.table i).1) outputs emitted.code

/-- Check a designated direct transfer row and the exact packed readback.
Original block and exit profiles stay in their original order. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) (selected : Fin blocks) :
    Option (Compiled sig context packets outputs source) :=
  letI := sig.typing
  if original : NamedFlat.check source context packets outputs = true then
    match (read sig packets outputs source selected).bind fun shape => (emit shape).map (Sigma.mk shape) with
    | none => none
    | some ⟨shape, emitted⟩ =>
      let profile := fun i => (shape.table i).1
      if typed : NamedFlat.check emitted.code context profile outputs = true then
        (construct sig profile outputs emitted.code).map fun packed =>
          ⟨shape, emitted, NamedFlat.check_sound _ _ _ _ original, NamedFlat.check_sound _ _ _ _ typed, packed⟩
      else none
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block
