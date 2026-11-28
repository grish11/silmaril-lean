module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Scope.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Row.Defs

/-! # Construct a public table and exact provenance from a flat readback -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open LambdaSSA (FiniteCFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link (Label)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
universe u

/-- Traverse consecutive indices without forgetting their attached types. -/
def tabulateDependent : (count : Nat) → {A : Fin count → Type u} →
    (∀ i, Option (A i)) → Option (∀ i, A i)
  | 0, _, _ => some (fun i => Fin.elim0 i)
  | count + 1, _, f => do
    let head ← f 0
    let tail ← tabulateDependent count (fun i => f i.succ)
    return Fin.cases head tail

variable {F : Type} {blocks exits captures : Nat}
  (signature : PrimitiveSignature F) (internal : Fin blocks → PacketType) (external : Fin exits → PacketType)

abbrev RowTable := ∀ i, Code signature (Sum.elim internal external) [internal i]

/-- Preserve the original block indices, heterogeneous packet profiles, and
ordered exits. The sole public entry carries the selected block's packet. -/
def publicProgram (start : Fin blocks) (rows : RowTable signature internal external) :
    Program signature (fun _ : Fin 1 => internal start) external where
  locals := blocks
  localType := internal
  entry _ := .inl start
  entryType _ := rfl
  block := rows

theorem publicProgram_compile_count (start : Fin blocks) (rows : RowTable signature internal external) :
    ((publicProgram signature internal external start rows).compile 0).blocks.length = blocks := by
  simp [publicProgram, Program.compile]

theorem publicProgram_exit_count (start : Fin blocks) (rows : RowTable signature internal external) :
    (publicProgram signature internal external start rows).exits.length = exits := by
  simp [publicProgram, Program.exits]

/-- Success carries the checked public entry and exact provenance for the
actual input table. The public program is built from the reified rows. -/
structure Constructed (source : FiniteCFG F blocks exits captures) where
  start : Fin blocks
  rows : RowTable signature internal external
  elaborated : ∀ i, elaborateRow (Sum.elim internal external) signature [internal i]
    (source.block i).erase = some (rows i)
  packed : Program.PackedEntry (publicProgram signature internal external start rows) 0
  provenance : Provenance source packed.target

def Constructed.program {source : FiniteCFG F blocks exits captures}
    (built : Constructed signature internal external source) :
    Program signature (fun _ : Fin 1 => internal built.start) external :=
  publicProgram signature internal external built.start built.rows

/-- The row at each generated position is the exact erased source row. -/
theorem Constructed.row_erasure {source : FiniteCFG F blocks exits captures}
    (built : Constructed signature internal external source) (i : Fin blocks) :
    (source.block i).erase = (built.packed.target.block (i.cast built.provenance.count)).erase :=
  (built.provenance.sourceRow i).trans (built.provenance.publicRow i).symm

def readEntry (source : FiniteCFG F blocks exits captures) :
    Option {s : Fin blocks × Silmaril.SSA.LambdaRTL.Val (Fin captures) //
      source.entry.erase = .br s.1.val (packetTerm s.2)} :=
  match source.entry with
  | .br label arg => do
    if inside : label.val < blocks then
      let seed ← seedValue arg
      return ⟨(⟨label.val, inside⟩, seed.val), congrArg (LambdaSSA.Region.br label.val) seed.property⟩
    else none
  | _ => none

/-- Traverse the actual flat table in index order, retaining the success
equation for each typed public row. -/
def elaborateRows (source : FiniteCFG F blocks exits captures) :
    Option (∀ i, {row : Code signature (Sum.elim internal external) [internal i] //
      elaborateRow (Sum.elim internal external) signature [internal i] (source.block i).erase = some row}) :=
  tabulateDependent blocks fun i =>
    match elaborateRow (Sum.elim internal external) signature [internal i] (source.block i).erase with
    | none => none
    | some row => some ⟨row, rfl⟩

def constructAt [DecidableEq F] (source : FiniteCFG F blocks exits captures)
    (start : Fin blocks) (seed : Silmaril.SSA.LambdaRTL.Val (Fin captures))
    (sourceEntry : source.entry.erase = .br start.val (packetTerm seed)) :
    Option (Constructed signature internal external source) :=
  match elaborateRows signature internal external source with
  | none => none
  | some results =>
    let rows : RowTable signature internal external := fun i => (results i).val
    let program := publicProgram signature internal external start rows
    let inputs : Fin 1 → Register := fun _ => ⟨0⟩
    let context : BoundCtx PacketType 1 := .snoc .nil (internal start)
    let count : blocks = (program.compile 0).blocks.length :=
      (publicProgram_compile_count signature internal external start rows).symm
    let exitCount : exits = program.exits.length :=
      (publicProgram_exit_count signature internal external start rows).symm
    let R := fun i => internal (i.cast count.symm)
    let L := fun i => external (i.cast exitCount.symm)
    match accepted : NamedFlat.elaborate (program.compile 0) program.exits inputs with
    | none => none
    | some target =>
      let _ := signature.typing
      if typed : NamedFlat.check target context R L = true then
        let packed : Program.PackedEntry program 0 :=
          ⟨1, inputs, context, R, L, target, accepted, NamedFlat.check_sound _ _ _ _ typed⟩
        let route := NamedFlat.labelIndex (program.compile 0).blocks program.exits ⟨.inl start⟩
        if label : route = some (start.cast count |>.castAdd program.exits.length) then
          match tabulateDependent blocks (fun i =>
              commonRow (blocks + exits) (source.block i).erase (target.block (i.cast count)).erase) with
          | none => none
          | some common =>
            some ⟨start, rows, fun i => (results i).property, packed,
              ⟨count, exitCount, start, seed, 0, sourceEntry,
                packedEntry_erase_entry packed 0 _ rfl label,
                fun i => (common i).val, fun i => (common i).property.1, fun i => (common i).property.2⟩⟩
        else none
      else none

/-- Reify every row with its exact profile, pass the actual public compile
output through ordinary elaboration and typing, and check row erasures. -/
def construct [DecidableEq F] (source : FiniteCFG F blocks exits captures) :
    Option (Constructed signature internal external source) :=
  match readEntry source with
  | none => none
  | some entry => constructAt signature internal external source entry.val.1 entry.val.2 entry.property

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
