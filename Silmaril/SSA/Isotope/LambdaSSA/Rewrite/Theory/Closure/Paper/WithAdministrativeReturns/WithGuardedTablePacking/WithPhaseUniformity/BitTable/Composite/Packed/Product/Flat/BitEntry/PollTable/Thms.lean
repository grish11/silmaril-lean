module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PollTable

/-! # Certificates for a reified fragment of cyclic flat sources

No seed and no quotient law is added. Nothing is inferred from a model
beyond the existing reflection for tidy router tables. Default Paper is
unchanged.

## The fragment

`PollTable` (see `Defs.lean`): two blocks with one Bit parameter each;
every block sends one request with its own label, querying its
parameter; each reply either leaves with the reply payload or jumps to a
block with it; the entry jumps to the start block with the input. From
one value `d : PollTable` both the scoped flat graph `d.flat` and the
router table `d.router` are computed.

## The certificate, for every table of the fragment

* `PollTable.flat_typed`: the graph is typed in the flat judgment.
* `PollTable.source_readback`: the source equals its packed readback, by
  the existing table-packing seed.
* `PollTable.readback_eqv_entered`: the packed readback is the router
  table entered at the start row, on the input as its Bit. **Default
  Paper**, in three steps:
  1. each readback row is the capture-free row of its block whiskered by
     the captured input and followed by `dropCase`, so #5314's
     `twoRows_iterate` drops the captured input;
  2. the loop on the two tags and the packed loop on `States 1` are
     related by a pair of maps, one a section of the other, and the roll
     law of iteration;
  3. on each row, the block with its exits tagged is the packed request
     of its label followed by the routing of its actions: congruence
     under the request, and a Bit as the case of its two constructors.
* `PollTable.source_eqv_entered`: so the source is the router table
  entered at the start row, in the table-packing quotient.
* `PollTable.bitPointed`: the certificate of #5332, with the same row at
  both constant inputs.

The only opt-in rule in the certificate is the packing seed, used once.
Unit η and phase uniformity are not used.

## Completeness

Every row of `d.router` is labelled, so the table is `Tidy`.

* `PollTable.complete`: two sources of the fragment are equal at the
  source entry exactly when they are valid in every supported model.
  This is #5332's theorem; it uses the existing reflection for tidy
  tables in the opt-in quotient.
* `PollTable.source_eqv_iff_entered`,
  `PollTable.source_eqv_iff_bisimulation`: they are equal exactly when
  the two router tables are equal at their start rows, that is, exactly
  when the tables are bisimilar from their start rows.

## Tables with different row actions

* `selfTable_eqv_swapTable`: a block that repeats itself and a block that
  goes to the other block give equal sources. The row actions differ and
  the labels do not.
* `selfTable_ne_neverTable`: a table that leaves on the left reply is
  not equal to one that never leaves, whatever the labels.

## Not covered

* **Recognition of syntax.** There is no function from a scoped flat
  graph to a `PollTable`. It needs a reader `read` on
  `FiniteCFG signature.Instr 2 1 1` that matches the entry jump and the
  two blocks, with the soundness statement `read g = some d → g = d.flat`.
  Nothing in the certificate depends on it. The flat syntax has no
  decidable equality, so the reader has to match constructors.
* More than two blocks. The reduction of the readback uses the two-row
  lemma of #5314 and the packed state `States 1`.
* Request-free blocks (silent forwarding), a block that uses the captured
  input, a reply branch that sends a constant or a computed Bit, an entry
  other than a jump with the input, and more than one exit.
* Tables that are not tidy do not occur here; the completeness theorem
  is otherwise limited to the supported models and the opt-in quotient.
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

namespace PollTable

variable (d d' : PollTable)

/-- The flat graph is typed in the flat judgment. -/
theorem flat_typed :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit) d.flat :=
  Tables.poll_flat_typed d

/-- The table-packing seed at the source. -/
theorem source_readback : WithGuardedTablePacking.Eqv false [Bit] d.source d.readback.val [Bit] :=
  Tables.poll_source_readback d

/-- The packed readback is the router table entered at the start row, on
the input as its Bit. Default Paper. -/
theorem readback_eqv_entered :
    Paper.Eqv [Bit] d.readback.val (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered (pairIdx d.start)))
      [Bit] :=
  Tables.poll_readback_eqv d

/-- The source is the router table entered at the start row, in the
table-packing quotient. -/
theorem source_eqv_entered :
    WithGuardedTablePacking.Eqv false [Bit] d.source
      (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered (pairIdx d.start))) [Bit] :=
  Tables.poll_source_entered d

/-- The certificate at the two constant inputs. -/
theorem bitPointed :
    BitPointed d.source (fun i => some (d.label (pairBit i))) d.act (fun _ => pairIdx d.start) :=
  Tables.poll_bitPointed d

/-- Two sources of the fragment are equal at the source entry exactly
when they are valid in every supported model. -/
theorem complete :
    Eqv false [Bit] d.source d'.source [Bit] ↔ Valid d.source_typed.hasType d'.source_typed.hasType :=
  Tables.poll_complete d d'

/-- They are equal exactly when their router tables are equal at the
start rows. -/
theorem source_eqv_iff_entered :
    Eqv false [Bit] d.source d'.source [Bit] ↔
      Eqv false [State] (d.router.entered (pairIdx d.start)) (d'.router.entered (pairIdx d'.start)) [Bit] :=
  Tables.poll_eqv_iff_entered d d'

/-- Exactly when the two tables are bisimilar from their start rows. -/
theorem source_eqv_iff_bisimulation :
    Eqv false [Bit] d.source d'.source [Bit] ↔
      ∃ R : Fin 2 → Fin 2 → Prop, (∀ x y, R x y → d.label (pairBit x) = d'.label (pairBit y)) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧
        R (pairIdx d.start) (pairIdx d'.start) :=
  Tables.poll_eqv_iff_bisim d d'

end PollTable

/-! ## Tables with different row actions -/

/-- Repeating the same block and going to the other block give equal sources. -/
theorem selfTable_eqv_swapTable (l : Bool) :
    Eqv false [Bit] (selfTable l).source (swapTable l).source [Bit] :=
  Tables.self_swap l

/-- A table that leaves on the left reply is not one that never leaves. -/
theorem selfTable_ne_neverTable (l l' : Bool) :
    ¬ Eqv false [Bit] (selfTable l).source (neverTable l').source [Bit] :=
  Tables.self_never l l'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
