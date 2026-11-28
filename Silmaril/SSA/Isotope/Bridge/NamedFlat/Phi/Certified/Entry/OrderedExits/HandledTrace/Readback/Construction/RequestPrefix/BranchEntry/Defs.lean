module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Defs

/-! # Move a checked structural entry into a public row -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchEntry

open LambdaSSA (FiniteCFG Flat Region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature elaborateBranch)

variable {F : Type} {blocks exits captures : Nat}

/-- The appended entry receives the canonical packed capture record. Old
rows keep their exact packet types and positions. -/
def profile (context : BoundCtx PacketType captures) (packets : Fin blocks → PacketType) :
    Fin (blocks + 1) → PacketType :=
  fun i => if old : i.val < blocks then packets ⟨i.val, old⟩ else Region.packedInputType context.toList

structure Materialized (context : BoundCtx PacketType captures) (source : FiniteCFG F blocks exits captures) where
  code : FiniteCFG F (blocks + 1) exits captures
  written : Flat F (blocks + 1 + exits) captures
  written_eq : written.erase = source.entry.erase.renameLabels (moveExit blocks 1)
  entry_eq : code.entry.erase = .br blocks (Region.packedInputValue context.toList)
  dispatch_eq : (code.block (Fin.last blocks)).erase = written.erase.packInputsDestructure context.toList
  row_eq : ∀ i : Fin blocks, (code.block i.castSucc).erase =
    (source.block i).erase.renameLabels (moveExit blocks 1)

/-- Append one dispatcher row. Its body is the actual written entry with
relocated targets, under the standard capture destructurer. -/
def materialize (context : BoundCtx PacketType captures) (source : FiniteCFG F blocks exits captures) :
    Option (Materialized context source) := do
  let labels := blocks + 1 + exits
  let written ← scopedRow labels captures (source.entry.erase.renameLabels (moveExit blocks 1))
  let entry ← scopedRow labels captures (.br blocks (Region.packedInputValue context.toList))
  let dispatch ← scopedRow labels (captures + 1) (written.val.erase.packInputsDestructure context.toList)
  let rows ← tabulateDependent blocks fun i =>
    scopedRow labels (captures + 1) ((source.block i).erase.renameLabels (moveExit blocks 1))
  let code : FiniteCFG F (blocks + 1) exits captures :=
    ⟨entry.val, fun i => if old : i.val < blocks then (rows ⟨i.val, old⟩).val else dispatch.val⟩
  return ⟨code, written.val, written.property, entry.property,
    by simpa only [code, Fin.val_last, Nat.lt_irrefl, dite_false] using dispatch.property,
    fun i => by simpa only [code, Fin.val_castSucc, dite_eq_left i.isLt] using (rows i).property⟩

structure Prepared (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  branch : CaseTail packets outputs context.toList
  elaborated : elaborateBranch (Sum.elim packets outputs) context.toList source.entry.erase = some branch
  emitted : Materialized context source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  emittedTyped : letI := sig.typing; emitted.code.HasType context (profile context packets) outputs

/-- Admit a written entry in the existing pure typed branch grammar.
Jump leaves are checked against their exact old packet or ordered exit type. -/
def prepare (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Prepared sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match accepted : elaborateBranch (Sum.elim packets outputs) context.toList source.entry.erase with
    | none => none
    | some branch => do
      let emitted ← materialize context source
      if typed : NamedFlat.check emitted.code context (profile context packets) outputs = true then
        some ⟨branch, accepted, emitted, NamedFlat.check_sound _ _ _ _ original, NamedFlat.check_sound _ _ _ _ typed⟩
      else none
  else none

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  prepared : Prepared sig context packets outputs source
  split : RequestPrefix.Checked sig context (profile context packets) outputs prepared.emitted.code
  publicReadback : Constructed sig (fun i => (split.shape.table i).1) outputs split.emitted.code

/-- Promote the entry, split the selected original row, and check the exact
erased rows of the resulting public packed program. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) (selected : Fin blocks) :
    Option (Compiled sig context packets outputs source) :=
  match prepare sig context packets outputs source with
  | none => none
  | some prepared =>
    match RequestPrefix.check sig context (profile context packets) outputs prepared.emitted.code
        (some selected.castSucc) with
    | none => none
    | some split =>
      (construct sig (fun i => (split.shape.table i).1) outputs split.emitted.code).map fun result =>
        ⟨prepared, split, result⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchEntry
