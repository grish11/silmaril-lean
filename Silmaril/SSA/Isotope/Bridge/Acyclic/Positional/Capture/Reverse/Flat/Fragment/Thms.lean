module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.FragmentReadback

/-! # The table of a delimited flat graph keeps its entry, jumps, exits and readback

The translation of a witnessed flat graph in the fragment keeps the
control structure of the graph. Every row jumps to the labels of its flat
block, in order: a block at the same index, an exit at the same position.
So the local targets of the table are those of the flat graph, and the
rank check of the flat graph is the check of the table. The entry of the
flat graph jumps to the first block, which is the entry row of the table.

The operands are folded: the lets of a flat block are inside the operand
of its row. The flat image of the table is therefore not the flat graph
itself. The two readbacks are natively equal all the same: the readback
of the checked table and the term that `FlatLetCase.compile` already
gives the flat graph, at the same captured context and the same packed
ordered exits.

The proof is local. A row is simulated under any vector of continuations
for the blocks: the flat compile of a block around the vector, weakened
along a scope, is natively equal to the table compile of its row at that
scope, when the table continuations agree with the vector at every scope.
A line moves its lets out of the jump by the sequencing laws. A fork
moves its lets out of the scrutinee, sequences the case of injections
before the case on the packet, and reduces each arm by case beta at its
injection; the continuation of each label is weakened beneath the payload
binder. The blocks then follow by induction on the checked rank of the
table, and the entry is a line into the first block. Only the derived
sequencing, case beta and case eta laws of the native theory are used;
no bound term has to be pure.

The equality is native equality of the two terms. The fragment is not
widened: a block that is not a row has no table.

Whether a witness is in the fragment depends on the flat graph only.
`delimitedShape` is that check on the flat graph, and a witness of a flat
graph of that shape is in the fragment.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open Positional
open Positional.Capture (Scope)
open SSA.FiniteSum (append)
open Region (packedExitType)
open LetCase.LocallyNameless (Equiv)
open Positional.Capture.Reverse (CheckedTable)

universe u v w

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

/-- Whether a witness is in the fragment depends on the flat graph only: a
witness of a flat graph of the shape of the fragment is in the fragment. -/
theorem Witness.delimited_of_shape (w : Witness g β R D) (shape : delimitedShape g = true) :
    w.Delimited :=
  delimited_of_shape_proof w shape

/-! ## Readback -/

variable {ε : Type w} [HasEff Φ ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- The row simulation. Fix any continuation `F j` for every block `j`,
over the captured context and the packet of the block. The flat compile
of a block around `F`, weakened along a scope, is natively equal to the
table compile of its row at that scope, for any table continuations that
agree with `F` at every scope. -/
theorem row_readback (pe : ε) {R : Fin blocks → τ}
    (F : ∀ j, Operand Φ (β.snoc (R j)) (packedExitType (List.ofFn D))) {P : τ}
    {t : Flat Φ (blocks + exits) (n + 1)} (b : Body Φ (append R D) (β.snoc P) t)
    (row : Positional.Capture.Block Φ β R (List.ofFn D) P) (h : b.row = some row) {k : Nat}
    {γ : BoundCtx τ k} (s : Scope β γ)
    (next : Positional.Capture.LocalContinuations β R (List.ofFn D) Φ row.locals)
    (agree : ∀ j (hj : j ∈ row.locals) {k' : Nat} {γ' : BoundCtx τ k'} (s' : Scope β γ'),
      Equiv pe Γ₀ (γ'.snoc (R j))
        ((F j).1.rename (LetCase.LocallyNameless.Tm.up s'.renaming.toFun))
        (next j hj s').encode.toLetCase.1 (packedExitType (List.ofFn D))) :
    Equiv pe Γ₀ (γ.snoc P)
      ((compileBody b (.skip .base P) (fun j _ => F j)).toLetCase.1.rename
        (LetCase.LocallyNameless.Tm.up s.renaming.toFun))
      (row.compile s next).encode.toLetCase.1 (packedExitType (List.ofFn D)) :=
  row_compile_proof pe F b row h s next agree

/-- The flat compile of a block, weakened along a scope, is natively equal
to the table compile of the block at that scope. -/
theorem Witness.block_readback (pe : ε) (w : Witness g β R D) (h : w.Delimited)
    (ranked : Rank.check (localTargets g) = true) (checked : (w.table h).check = true)
    (i : Fin (size + 1)) {k : Nat} {γ : BoundCtx τ k} (s : Scope β γ) :
    Equiv pe Γ₀ (γ.snoc (R i))
      ((compileAt w ranked i).toLetCase.1.rename (LetCase.LocallyNameless.Tm.up s.renaming.toFun))
      ((w.table h).compileAt checked i s).encode.toLetCase.1 (packedExitType (List.ofFn D)) :=
  block_readback_proof pe w h ranked checked _ i (Nat.lt_succ_self _) s

/-- The readback of the checked table of a flat graph in the fragment is
natively equal to the term that the flat graph already has. -/
theorem Witness.checkedTable_readback (pe : ε) (w : Witness g β R D) (h : w.Delimited)
    (ranked : Rank.check (localTargets g) = true) (checked : (w.table h).check = true) :
    Equiv pe Γ₀ β (compile w ranked).toLetCase.1 (w.checkedTable h checked).toLetCase.1
      (packedExitType (List.ofFn D)) :=
  checkedTable_readback_proof pe w h ranked checked

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
