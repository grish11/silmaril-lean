module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Defs

/-! # Source-local checks for reversion -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

/-- Recognize the straight-line subset, with a jump as the final terminator. -/
def bodySupported {V K : Type u} {F : Type v} : CFG.Body V K F → Bool
  | .let1 _ _ tail | .let2 _ _ _ tail => bodySupported tail
  | .term (.br ..) => true
  | .term (.case ..) => false

variable {Base V K : Type u} {F : Type v} {n labels : Nat}
  [DecidableEq V] [DecidableEq Base] [HasTy F (Ty Base)]

/-- Check an unversioned body in its original argument and capture context.
The named terminator grammar supports jumps and nested sum cases. -/
def sourceCheck (index : K → Option (Fin labels)) (types : Fin labels → Ty Base)
    (names : Names V n) (ctx : BoundCtx (Ty Base) n) (src : CFG.Body V K F) : Bool :=
  ((NamedFlat.body index names src).map (checkBody types ctx)).getD false

/-- Check a named entry and every row against a supplied label numbering. -/
def checkSourceRows (graph : CFG V K F) {count : Nat} (order : graph.blocks.length = count)
    (names : Fin n → V) (ctx : BoundCtx (Ty Base) n) (R : Fin count → Ty Base)
    {exits : Nat} (external : Fin exits → Ty Base) (index : K → Option (Fin (count + exits))) : Bool :=
  let types := SSA.FiniteSum.append R external
  sourceCheck index types (first names) ctx graph.entry &&
    (List.finRange count).all fun i =>
      let b := graph.blocks[Fin.cast order.symm i].2
      sourceCheck index types (blockNames b.param) (.snoc ctx (R i)) b.body

/-- Check the original arguments, captures and exits at the packet-local
versioner's label numbering. Each row starts with only its parameter in scope. -/
def packetLocalSourceChecks [DecidableEq K] (graph : CFG V K F) (names : Fin n → V)
    (ctx : BoundCtx (Ty Base) n) (exits : List K) (external : Fin exits.length → Ty Base)
    (R : Fin (Versioning.compilePacketLocal graph).blocks.length → Ty Base) : Bool :=
  checkSourceRows graph (List.length_map _).symm names ctx R external
    (labelIndex (Versioning.compilePacketLocal graph).blocks exits)

variable {κ K : Type (u + 1)} [DecidableEq K] [DecidableEq κ]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : LambdaSSA.FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => Versioning.compile attached
local notation "exitTypes" => Interface.external
  (LiveOut.exitInterface (numberedInterface context exits external) fields)

/-- Check the source rows against a label numbering with the same row count. -/
def checkRows {count : Nat} (order : (attached).blocks.length = count)
    (R : Fin count → Ty κ) (index : K → Option (Fin (count + exits.length))) : Bool :=
  checkSourceRows attached order (fun i => (⟨i.val⟩ : Register)) context R exitTypes index

/-- Check the original entry and every original block with their original
packet types. Use the versioned label order, which retains the written
block order, to avoid a separate numbering in the local checks. -/
def checks (R : Fin blocks → Ty κ) : Bool :=
  checkRows a (List.length_map _).symm (fun i => R (Fin.cast a.reversionCount i))
    (labelIndex (versioned).blocks exits)

local notation "packetLocal" => Versioning.compilePacketLocal attached

omit [DecidableEq κ] in
/-- The opt-in compiler preserves the written block count and order. -/
theorem packetLocalCount : (packetLocal).blocks.length = blocks :=
  (List.length_map _).trans a.count

/-- The actual installed profile pairs each original argument with unit. -/
def packetLocalProfile (R : Fin blocks → Ty κ)
    (i : Fin (packetLocal).blocks.length) : Ty κ :=
  .product (R (Fin.cast (packetLocalCount a) i)) .unit

/-- Check the original bodies at the opt-in compiler's label numbering,
using the original argument and exit types. -/
def packetLocalChecks (R : Fin blocks → Ty κ) : Bool :=
  packetLocalSourceChecks attached (fun i : Fin n => (⟨i.val⟩ : Register)) context exits exitTypes
    (fun i => R (Fin.cast (packetLocalCount a) i))

/-- The selected input register has no assignment or case binder in the
attached entry or block bodies. Packet parameters are checked by the actual
saved slot lists. -/
def keepsEntryCapture (slot : Fin n) : Bool :=
  let reg : Register := ⟨slot.val⟩
  decide (reg ∉ (attached).entry.toRegion.bound) &&
    (attached).blocks.all (fun block => decide (reg ∉ block.2.body.toRegion.bound))

/-- The unchanged entry registers and their types in the saved packet order. -/
def captureFields (ctx : BoundCtx (Ty κ) n) (slots : List (Fin n)) : List (Register.{u} × Ty κ) :=
  slots.map fun i => (⟨i.val⟩, ctx.get i)

/-- Check that the selected input slots are unassigned in all attached bodies. -/
def keepsEntryCaptures (slots : List (Fin n)) : Bool :=
  slots.all (keepsEntryCapture a)

/-- Select the first matching internal destination, in the same label order
as the actual versioner. Unmatched labels carry no saved entry slots. -/
def destinationSlots (layouts : Fin (versioned).blocks.length → List (Fin n)) (label : K) : List (Fin n) :=
  (((versioned).blocks.findFinIdx? (fun item => label == item.1)).map layouts).getD []

/-- Every emitted internal edge asks only for slots saved by its source
block. The jump packs those slots in the destination's checked order. -/
def checksCaptureEdges (layouts : Fin (versioned).blocks.length → List (Fin n)) : Bool :=
  (List.finRange (versioned).blocks.length).all fun i =>
    let block := (attached).blocks[Fin.cast (List.length_map _) i].2
    block.body.targets.all fun label =>
      (destinationSlots a layouts label).all (fun slot => decide (slot ∈ layouts i))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
