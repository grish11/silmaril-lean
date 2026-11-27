module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Controlled.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ControlledSource

/-! # A two-block flat source whose captured input chooses the request

No seed and no quotient law is added. Nothing is inferred from a model.
Default Paper is unchanged. The results are for this family of sources;
nothing is claimed for capture-dependent tables in general.

## The source

`ctrlFlat l₀ l₁` is a scoped flat graph with two blocks, one exit and
one captured Bit `c`. The header cases on `c` and sends the request `l₀`
or `l₁`, with its live parameter as the query in both cases. On the left
reply it leaves with `c`; on the right reply it jumps to the back-edge
block, which jumps back. The captured input controls a reachable request:
the two labels are independent parameters. `ctrlFlat_typed` types the
graph in the flat judgment.

## The row transport

The header row is not a capture-free row followed by a common tail: its
request depends on the captured input. #5323's `twoRows_keep` does not
apply and is not used on this row.

* `ctrlSource_const`: at a constant input `q`, the source is the source
  of #5323 with the label `pickLabel l₀ l₁ q`. Inside the table the
  header's case on the captured input becomes a case on a constructor.
  The proof is congruence of the two-block table on its header block and
  the native case on a constructor: an equation of **default Paper**
  between two tables with two blocks. This is the capture-sensitive step.

## The router table at each input

`ctrlRouter l₀ l₁` has two rows; row `c` sends `pickLabel l₀ l₁ c` and
stays in its row.

* `ctrlSource_pointed`: at each constant input `q` the source is this
  table entered at the row of `q`, carrying `q`. It combines
  `ctrlSource_const`, #5327's pointed result for the chosen label, and a
  bisimulation between the one-label and the two-label table at that row.

## Completeness at the source entry

* `ctrlSource_labels_of_valid`: validity at the source entry determines
  both labels. The two constant inputs reach the two rows; at each, the
  query-aware model shows the first request label. The two labels are
  separated independently.
* `ctrlSource_complete`: two sources are equal at the source entry
  exactly when they are valid in every supported model.
* `ctrlSource_eqv_iff`: they are equal exactly when both labels agree.

## The loop on the pair

`ctrlBody l₀ l₁` is the step on the pair of captured input and header
parameter, with the same case on the first component.

* `ctrlBody_step`: conjugated by the encoding of pairs, it is the
  dispatcher step of `ctrlRouter l₀ l₁`. At row `c` product β and the
  case on a constant give #5327's row with the label of `c`.
* `ctrlLoop_factors`, `ctrlLoop_complete`: factoring through the packed
  loop, and completeness at the product-state entry.
* `ctrlSource_eqv_loop`: the source equals `ctrlLoop l₀ l₁` at the
  source entry, in the opt-in quotient. Both agree with the router table
  at each constant input, and unit η recombines the two inputs.

All of these except `ctrlSource_const` use the opt-in quotient: the
packing seed (through #5323), unit η and phase uniformity.

## Not covered

* A default-Paper equation, after the seed, between the packed readback
  of this source and a loop. The correspondence with `ctrlLoop` goes
  through the two constant inputs.
* A captured input that is not a Bit, or is not split into finitely many
  constants.
* A header whose query is the captured input, more blocks, more exits.
* Capture-dependent tables in general, and completeness in default Paper.
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

/-! ## The source -/

/-- The flat graph is typed in the flat judgment. -/
theorem ctrlFlat_typed (l₀ l₁ : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit)
      (ctrlFlat l₀ l₁) :=
  Tables.ctrl_flat_typed l₀ l₁

/-! ## The row transport, in default Paper -/

/-- At a constant input the source is the source of #5323 with the label
chosen by that input. -/
theorem ctrlSource_const (l₀ l₁ q : Bool) :
    Paper.Eqv [Ty.unit] (seqRegion (.br 0 (bitTm q)) (ctrlSource l₀ l₁))
      (seqRegion (.br 0 (bitTm q)) (captSource (pickLabel l₀ l₁ q))) [Bit] :=
  Tables.ctrl_const l₀ l₁ q

/-! ## The router table and completeness at the source entry -/

/-- At each constant input the source is the two-label router table
entered at the row of that constant, carrying that constant. -/
theorem ctrlSource_pointed (l₀ l₁ : Bool) :
    SpinPointed (seqRegion (unpackExits [Bit]) (ctrlSource l₀ l₁))
      (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct pairIdx :=
  Tables.ctrl_pointed l₀ l₁

/-- Validity at the source entry determines both request labels. -/
theorem ctrlSource_labels_of_valid (l₀ l₁ l₀' l₁' : Bool)
    (v : Valid (ctrlSource_typed l₀ l₁).hasType (ctrlSource_typed l₀' l₁').hasType) :
    l₀ = l₀' ∧ l₁ = l₁' :=
  Tables.ctrl_labels_of_valid l₀ l₁ l₀' l₁' v

/-- Two sources are equal at the source entry exactly when they are
valid in every supported model. -/
theorem ctrlSource_complete (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlSource l₀' l₁') [Bit] ↔
      Valid (ctrlSource_typed l₀ l₁).hasType (ctrlSource_typed l₀' l₁').hasType :=
  Tables.ctrl_source_complete l₀ l₁ l₀' l₁'

/-- They are equal exactly when both request labels agree. -/
theorem ctrlSource_eqv_iff (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlSource l₀' l₁') [Bit] ↔ l₀ = l₀' ∧ l₁ = l₁' :=
  Tables.ctrl_source_eqv_iff l₀ l₁ l₀' l₁'

/-! ## The loop on the pair -/

/-- The step on the pair, conjugated by the encoding of pairs, is the
dispatcher step of the two-label router table. -/
theorem ctrlBody_step (l₀ l₁ : Bool) :
    Eqv false [States 1] (seqRegion pairDec (seqRegion (ctrlBody l₀ l₁) (postRegion pairEnc)))
      (dispatch 1 (ctrlRouter l₀ l₁).rows) [Silmaril.coprod Bit (States 1)] :=
  Tables.ctrl_step l₀ l₁

/-- The loop on the pair factors through the packed loop of its router table. -/
theorem ctrlLoop_factors (l₀ l₁ : Bool) :
    Factors pairDec (loopRegion Pair (ctrlBody l₀ l₁)) (ctrlRouter l₀ l₁) :=
  Tables.ctrl_factors l₀ l₁

/-- Two loops on the pair are equal at the product-state entry exactly
when they are valid in every supported model. -/
theorem ctrlLoop_complete (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Pair] (loopRegion Pair (ctrlBody l₀ l₁)) (loopRegion Pair (ctrlBody l₀' l₁')) [Bit] ↔
      Valid (loopRegion_typed (ctrlBody_typed l₀ l₁)).hasType
        (loopRegion_typed (ctrlBody_typed l₀' l₁')).hasType :=
  Tables.ctrl_complete l₀ l₁ l₀' l₁'

/-- The source is the loop on the pair of captured input and header
parameter at the source entry, in the opt-in quotient. -/
theorem ctrlSource_eqv_loop (l₀ l₁ : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlLoop l₀ l₁) [Bit] :=
  Tables.ctrl_source_loop l₀ l₁

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
