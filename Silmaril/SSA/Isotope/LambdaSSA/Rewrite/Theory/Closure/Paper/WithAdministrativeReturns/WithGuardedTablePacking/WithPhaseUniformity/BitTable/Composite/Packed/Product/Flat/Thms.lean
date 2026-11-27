module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.FlatSource

/-! # A cyclic flat source with two live Bits, and the loop on pairs

No seed and no quotient law is added. Nothing is inferred from a model.
Default Paper is unchanged.

## The source

`pairNamed l` is a named cyclic table with one header block and a back
edge. The header has two live Bits: it receives a pair `(x, y)`, sends
the request `l` with `y`, leaves with `x` on the left reply, and jumps
back to itself with `(r, x)` on the right reply `r`.

* `pairNamed_elaborate`: the existing elaborator of named cyclic tables
  turns it into the scoped flat graph `pairFlat l`.
* `pairFlat_typed`: that graph is typed in the flat judgment.
* `pairSource l` is its region, a guarded table (`pairSource_typed`).

The source is written with labels and a back edge. It is not obtained
from `pairBody` or from a loop region.

## One-header flat loops, in default Paper

`flatLoop_eqv_loop`: a flat table with one header block, entered at the
header with its input, is the loop whose step is the block with its two
labels tagged into a sum (`flatStep`). The proof is congruence of the
table on its block and the native case on a constructor. It holds for
any header block that does not use the captured input, not only for the
block of this source.

`Factors.of_flat`: with #5302's conjugacy lemma, such a table factors
through the packed loop of a router table once the conjugated step is the
dispatcher step.

## The source and the loop on pairs

* `pairSource_eqv_loop`: the source equals the loop on pairs at the
  source entry. An equation of default Paper.
* `pairSource_factors`: the source factors through the packed loop of
  `pairRouter l`.
* `pairSource_complete`: two sources are equal at the source entry
  exactly when they are valid in every supported model.
* `pairSource_eqv_iff`, `pairSource_eqv_loop_iff`: two sources, or a
  source and a loop on pairs, are equal exactly when their requests have
  the same label.

The last three use the opt-in quotient: unit η and phase uniformity,
through #5306.

## The packed readback, and what it does not give

* `pairSource_readback`: the table-packing seed at the source.
* `pairReadback_eqv_loop`: the packed readback equals the loop on pairs.
  The proof goes through the source: the seed backwards, then the native
  equation.
* `pairReadback_eqv_iff`: two packed readbacks are equal exactly when the
  requests have the same label.
* `pairReadback_state`: the packed readback is a routed entry followed
  by a loop on `ReadbackState`, the captured input paired with the tagged
  parameter of the header. That loop is not a loop on the two Bits.

For this source the native equation does not use the seed. No equation
between the readback loop on `ReadbackState` and a loop on the header
parameter is proved here except through the source.

## Not covered

* A table with more than one block. `flatLoop_eqv_loop` is congruence on
  one block; for several blocks the checked route is the packed readback,
  whose loop carries the captured input and the tags of all blocks.
  Relating that loop to a loop on the parameters is not proved, and
  nothing is claimed about whether it can be.
* A header block that uses the captured input, an entry other than the
  jump to the header with the input, and more than one exit.
* The flat judgment accepts any typed argument at a jump; a guarded table
  needs a constructor value there. This source has constructor values.
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

variable {S : Ty Empty} {K : Nat} {b enc dec : Region signature.Instr}

/-! ## One-header flat loops, in default Paper -/

/-- A flat table with one header block, entered at the header with its
input, is the loop of the header's step, at the source entry. -/
theorem flatLoop_eqv_loop (hb : ValueBranches [S] b [S, Bit]) :
    Paper.Eqv [S] (flatLoop b) (loopRegion S (flatStep b)) [Bit] :=
  Tables.flat_loop hb

/-- A one-header flat table whose step, conjugated by an encoding with a
section, is the dispatcher step of a router table, factors through the
packed loop of that table. -/
theorem Factors.of_flat (he : ValueBranches [S] enc [States K]) (hd : ValueBranches [States K] dec [S])
    (hb : ValueBranches [S] b [S, Bit]) (ret : Retracts S enc dec) (t : Router K)
    (hstep : Eqv false [States K] (seqRegion dec (seqRegion (flatStep b) (postRegion enc))) (dispatch K t.rows)
      [Silmaril.coprod Bit (States K)]) : Factors dec (flatLoop b) t :=
  Tables.flat_factors he hd hb ret t hstep

/-! ## The source -/

/-- The named cyclic table elaborates to the flat graph, with the exit
list `[exit]` and the input register `p` as the captured variable. -/
theorem pairNamed_elaborate (l : Bool) :
    Bridge.NamedFlat.elaborate (pairNamed l) [.exit] (fun _ : Fin 1 => PairReg.p) = some (pairFlat l) :=
  Tables.named_flat l

/-- The flat graph is typed in the flat judgment: the header receives a
pair, the exit a Bit, and the captured input is a pair. -/
theorem pairFlat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Pair) (fun _ : Fin 1 => Pair) (fun _ : Fin 1 => Bit)
      (pairFlat l) :=
  Tables.flat_typed l

/-! ## The source and the loop on pairs -/

/-- The flat source is the loop on pairs at the source entry, in default Paper. -/
theorem pairSource_eqv_loop (l : Bool) :
    Paper.Eqv [Pair] (pairSource l) (loopRegion Pair (pairBody l)) [Bit] :=
  Tables.source_loop l

/-- The flat source factors through the packed loop of its router table. -/
theorem pairSource_factors (l : Bool) : Factors pairDec (pairSource l) (pairRouter l) :=
  Tables.source_factors l

/-- Two flat sources are equal at the source entry exactly when they are
valid in every supported model. -/
theorem pairSource_complete (l l' : Bool) :
    Eqv false [Pair] (pairSource l) (pairSource l') [Bit] ↔
      Valid (pairSource_typed l).hasType (pairSource_typed l').hasType :=
  Tables.source_complete l l'

/-- They are equal exactly when their requests have the same label. -/
theorem pairSource_eqv_iff (l l' : Bool) :
    Eqv false [Pair] (pairSource l) (pairSource l') [Bit] ↔ l = l' :=
  Tables.source_eqv_iff l l'

/-- A flat source and a loop on pairs are equal exactly when their
requests have the same label. -/
theorem pairSource_eqv_loop_iff (l l' : Bool) :
    Eqv false [Pair] (pairSource l) (loopRegion Pair (pairBody l')) [Bit] ↔ l = l' :=
  Tables.source_loop_iff l l'

/-! ## The packed readback -/

/-- The table-packing seed at the flat source. -/
theorem pairSource_readback (l : Bool) :
    WithGuardedTablePacking.Eqv false [Pair] (pairSource l) (pairReadback l).val [Bit] :=
  Tables.source_readback l

/-- The packed readback of the flat source is the loop on pairs. The
proof goes through the source. -/
theorem pairReadback_eqv_loop (l : Bool) :
    WithGuardedTablePacking.Eqv false [Pair] (pairReadback l).val (loopRegion Pair (pairBody l)) [Bit] :=
  Tables.readback_loop l

/-- Two packed readbacks are equal exactly when the requests have the
same label. -/
theorem pairReadback_eqv_iff (l l' : Bool) :
    Eqv false [Pair] (pairReadback l).val (pairReadback l').val [Bit] ↔ l = l' :=
  Tables.readback_eqv_iff l l'

/-- The packed readback is a routed entry followed by a loop on
`ReadbackState`: the captured input paired with the tagged parameter of
the header. -/
theorem pairReadback_state (l : Bool) :
    ∃ route step : Region signature.Instr,
      ValueBranches [Pair] route [Silmaril.coprod Bit ReadbackState] ∧
      ValueBranches [ReadbackState] step [Silmaril.coprod Bit ReadbackState] ∧
      (pairReadback l).val = seqRegion route
        (.case (.var 0) (.br 0 (.var 0)) ((loopRegion ReadbackState step).renameVars (lift Nat.succ))) :=
  Tables.readback_state l

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
