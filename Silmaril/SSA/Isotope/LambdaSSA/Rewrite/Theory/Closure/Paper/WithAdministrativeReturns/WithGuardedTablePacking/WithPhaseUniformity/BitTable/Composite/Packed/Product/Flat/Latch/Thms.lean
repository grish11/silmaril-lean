module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Projection.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.LatchSource

/-! # A two-block cyclic flat source and the loop on pairs

No seed and no quotient law is added. Nothing is inferred from a model.
Default Paper is unchanged.

## The source

`latchNamed l` is a named cyclic table with two blocks. The header
`head` has two live Bits: it receives a pair `(x, y)`, sends the request
`l` with `y`, leaves with `x` on the left reply, and jumps to the block
`latch` with `(r, x)` on the right reply `r`. The block `latch` has its
own parameter and jumps back to `head` with it. Neither block uses the
captured input.

* `latchNamed_elaborate`: the existing elaborator of named cyclic tables
  turns it into the scoped flat graph `latchFlat l`.
* `latchFlat_typed`: that graph is typed in the flat judgment.
* `latchSource l` is its region, a guarded table with two blocks
  (`latchSource_typed`).

## The route

The step from a table of two blocks to one loop is the existing
table-packing seed. It is not proved in default Paper here:

* `latchSource_readback`: the source equals its packed readback.

Everything after the seed is default Paper.

* **Capture irrelevance.** `twoRows_iterate`: a two-row dispatcher whose
  rows thread a captured input without using it iterates as the step of
  the rows on the tags alone, after the input is dropped. The hypothesis
  on a row is checked: the row is the capture-free row whiskered by the
  input and followed by `dropCase`. The proof distributes the input over
  the tags, uses the projection law of iteration for a retained factor,
  and uses initiality for the empty tail. It is stated for any input
  type, row types and exit type. It does not cover a row that uses the
  captured input.
* `latchReadback_capture_free`: so the readback enters, at the tag of the
  header, the capture-free loop on the tags.
* **Block elimination.** `latchReadback_eqv_loop`: that loop is the loop
  on pairs, by the Bekič law for two blocks at an exact sum: the
  back-edge block is solved first and iterates to the header. So the
  packed readback equals `loopRegion Pair (pairBody l)` in default Paper.

## The source and the loop on pairs

* `latchSource_eqv_loop`: the source equals the loop on pairs at the
  source entry, in the table-packing quotient: the seed once, then
  default Paper.
* `latchSource_factors`: the source factors through the packed loop of
  `pairRouter l`.
* `latchSource_complete`: two sources are equal at the source entry
  exactly when they are valid in every supported model.
* `latchSource_eqv_iff`, `latchSource_eqv_loop_iff`,
  `latchSource_eqv_pairSource_iff`: two two-block sources, a two-block
  source and a loop on pairs, or a two-block source and the one-header
  source of #5309, are equal exactly when their requests have the same
  label.

The last four use the opt-in quotient: unit η and phase uniformity,
through #5306.

## Not covered

* The reduction of this table without the table-packing seed. It is not
  proved in default Paper, and nothing is claimed about whether it can be.
* A block that uses the captured input. `twoRows_iterate` needs each row
  in the lifted form.
* Tables with more than two blocks, an entry other than the jump to the
  header with the input, and more than one exit. `twoRows_iterate` is
  stated for two rows.
* Completeness in default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
open Silmaril.DeBruijn (lift)
open CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (iterate sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Projection (productSnd)

/-! ## The source -/

/-- The named two-block table elaborates to the flat graph, with the
exit list `[exit]` and the input register `p` as the captured variable. -/
theorem latchNamed_elaborate (l : Bool) :
    Bridge.NamedFlat.elaborate (latchNamed l) [.exit] (fun _ : Fin 1 => LatchReg.p) = some (latchFlat l) :=
  Tables.named_latch l

/-- The flat graph is typed in the flat judgment: both blocks receive a
pair, the exit a Bit, and the captured input is a pair. -/
theorem latchFlat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Pair) (fun _ : Fin 2 => Pair) (fun _ : Fin 1 => Bit)
      (latchFlat l) :=
  Tables.latch_flat_typed l

/-! ## Capture irrelevance, in default Paper -/

/-- A dispatcher of two rows that thread a captured input without using
it iterates as the capture-free step on the tags, after the input is
dropped. Each row is the capture-free row whiskered by the input and
followed by `dropCase`. -/
theorem twoRows_iterate {X A₀ A₁ D : Ty Empty} {ρ₀ ρ₁ dR β₀ β₁ : Region signature.Instr}
    (hρ₀ : ValueBranches [Silmaril.product X A₀] ρ₀
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (hρ₁ : ValueBranches [Silmaril.product X A₁] ρ₁
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (hd : ValueBranches [Silmaril.empty] dR
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (hβ₀ : ValueBranches [A₀] β₀
      [Silmaril.coprod D (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))])
    (hβ₁ : ValueBranches [A₁] β₁
      [Silmaril.coprod D (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))])
    (e₀ : ofRegion hρ₀ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₀)
      (dropCase_typed (X := X) (B := D) (A := Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))))
    (e₁ : ofRegion hρ₁ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₁)
      (dropCase_typed (X := X) (B := D) (A := Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))))
    (hdisp : ValueBranches [Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))]
      (twoRows ρ₀ ρ₁ dR)
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))]) :
    iterate (ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D
        (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))).hom) =
      productSnd (ofType (Φ := signature.Instr) X)
          (ofType (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))) ≫
        iterate (freeStep hβ₀ hβ₁) :=
  Tables.two_row_drop hρ₀ hρ₁ hd hβ₀ hβ₁ e₀ e₁ hdisp

/-- The packed readback enters, at the tag of the header, the
capture-free loop on the tags. Default Paper. -/
theorem latchReadback_capture_free (l : Bool) :
    ofRegion (latchReadback l).property =
      ofRegion tagHead_typed ≫ iterate (freeStep (headStep_typed l) latchStep_typed) :=
  Tables.readback_arrow l

/-! ## Block elimination, in default Paper -/

/-- The packed readback of the two-block source is the loop on pairs, in
default Paper: capture irrelevance, then Bekič for the two blocks. -/
theorem latchReadback_eqv_loop (l : Bool) :
    Paper.Eqv [Pair] (latchReadback l).val (loopRegion Pair (pairBody l)) [Bit] :=
  Tables.latch_readback_loop l

/-! ## The source and the loop on pairs -/

/-- The table-packing seed at the two-block source. -/
theorem latchSource_readback (l : Bool) :
    WithGuardedTablePacking.Eqv false [Pair] (latchSource l) (latchReadback l).val [Bit] :=
  Tables.latch_source_readback l

/-- The two-block source is the loop on pairs at the source entry, in
the table-packing quotient. -/
theorem latchSource_eqv_loop (l : Bool) :
    WithGuardedTablePacking.Eqv false [Pair] (latchSource l) (loopRegion Pair (pairBody l)) [Bit] :=
  Tables.latch_source_loop l

/-- The two-block source factors through the packed loop of its router table. -/
theorem latchSource_factors (l : Bool) : Factors pairDec (latchSource l) (pairRouter l) :=
  Tables.latch_factors l

/-- Two two-block sources are equal at the source entry exactly when
they are valid in every supported model. -/
theorem latchSource_complete (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (latchSource l') [Bit] ↔
      Valid (latchSource_typed l).hasType (latchSource_typed l').hasType :=
  Tables.latch_complete l l'

/-- They are equal exactly when their requests have the same label. -/
theorem latchSource_eqv_iff (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (latchSource l') [Bit] ↔ l = l' :=
  Tables.latch_eqv_iff l l'

/-- A two-block source and a loop on pairs are equal exactly when their
requests have the same label. -/
theorem latchSource_eqv_loop_iff (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (loopRegion Pair (pairBody l')) [Bit] ↔ l = l' :=
  Tables.latch_loop_iff l l'

/-- A two-block source and a one-header source are equal exactly when
their requests have the same label. -/
theorem latchSource_eqv_pairSource_iff (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (pairSource l') [Bit] ↔ l = l' :=
  Tables.latch_header_iff l l'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
