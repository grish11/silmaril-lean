module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment

/-! # The table of a delimited flat graph keeps its entry, jumps and exits

The translation of a witnessed flat graph in the fragment keeps the
control structure of the graph. Every row jumps to the labels of its flat
block, in order: a block at the same index, an exit at the same position.
So the local targets of the table are those of the flat graph, and the
rank check of the flat graph is the check of the table. The entry of the
flat graph jumps to the first block, which is the entry row of the table.

The operands are folded: the lets of a flat block are inside the operand
of its row. The flat image of the table is therefore not the flat graph
itself. There is no theorem here that the readback of the table is
natively equal to the readback that the flat graph already has; that is
checked on instances.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open Positional
open SSA.FiniteSum (append)
open Positional.Capture.Reverse (CheckedTable)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits n : Nat} {β : BoundCtx τ n} {D : Fin exits → τ}

omit [TypeFormers τ] in
/-- The target of a label has the index of the label: a block keeps its
index and an exit keeps its position. -/
theorem labelTarget_flatIndex {R : Fin blocks → τ} (i : Fin (blocks + exits)) :
    (labelTarget R D i).flatIndex List.length_ofFn = i :=
  labelTarget_flatIndex_proof i

/-- The row of a flat block jumps to the labels of the block, in order. -/
theorem row_jumps {R : Fin blocks → τ} {P : τ} {t : Flat Φ (blocks + exits) (n + 1)}
    (b : Body Φ (append R D) (β.snoc P) t) (row : Positional.Capture.Block Φ β R (List.ofFn D) P)
    (h : b.row = some row) : jumps (row.toFlat List.length_ofFn) = jumps t :=
  row_jumps_proof b row h

/-- The row of a flat block has the local targets of the block. -/
theorem row_locals {R : Fin blocks → τ} {P : τ} {t : Flat Φ (blocks + exits) (n + 1)}
    (b : Body Φ (append R D) (β.snoc P) t) (row : Positional.Capture.Block Φ β R (List.ofFn D) P)
    (h : b.row = some row) : row.locals = targets t :=
  row_locals_proof b row h

variable {size : Nat} {R : Fin (size + 1) → τ} {g : FiniteCFG Φ (size + 1) exits n}

/-- Every row of the table jumps to the labels of its flat block, in
order. -/
theorem Witness.table_jumps (w : Witness g β R D) (h : w.Delimited) (i : Fin (size + 1)) :
    jumps (((w.table h).block i).toFlat List.length_ofFn) = jumps (g.block i) :=
  table_jumps_proof w h i

/-- The entry of a flat graph in the fragment jumps to the first block
only. -/
theorem Witness.entry_jumps (w : Witness g β R D) (h : w.Delimited) :
    jumps g.entry = [Fin.castAdd exits 0] :=
  entry_jumps_proof w h

/-- The table has the local targets of the flat graph, row by row. -/
theorem Witness.table_localTargets (w : Witness g β R D) (h : w.Delimited) (i : Fin (size + 1)) :
    (w.table h).localTargets i = localTargets g i :=
  table_localTargets_proof w h i

/-- The rank check of the flat graph is the check of the table. -/
theorem Witness.table_check (w : Witness g β R D) (h : w.Delimited)
    (ranked : Rank.check (localTargets g) = true) : (w.table h).check = true :=
  table_check_proof w h ranked

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
