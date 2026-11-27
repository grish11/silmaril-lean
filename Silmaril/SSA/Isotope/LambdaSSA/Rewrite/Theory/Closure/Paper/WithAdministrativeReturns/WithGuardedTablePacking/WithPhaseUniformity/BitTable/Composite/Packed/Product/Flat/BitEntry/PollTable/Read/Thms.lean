module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Read.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PollRead

/-! # The reader of the polling fragment, and sources given as flat syntax

No seed and no quotient law is added. Default Paper is unchanged.

## The reader is exact

`PollTable.read` matches the constructors of a scoped flat graph with two
blocks, one exit and one captured input.

* `PollTable.read_sound`: if `read g = some d` then `g = d.flat`.
* `PollTable.read_flat`: `read d.flat = some d`.
* `PollTable.read_eq_some_iff`: `read g = some d ↔ g = d.flat`.

Both are equalities of syntax. No transport is needed: the table returned
for `d.flat` is `d` itself, by extensionality of its two functions on
Bits.

## Sources given as flat syntax

For graphs `g`, `g'` that the reader accepts, with tables `d`, `d'`:

* `PollTable.read_typed`: the region of `g` is a guarded source.
* `PollTable.read_bitPointed`: the certificate of #5332 for the region
  of `g`.
* `PollTable.read_source_eqv_entered`: the region of `g` is the router
  table of `d` entered at its start row, in the table-packing quotient.
* `PollTable.read_complete`: the regions of `g` and `g'` are equal at the
  source entry exactly when they are valid in every supported model.
* `PollTable.read_eqv_iff_bisimulation`: exactly when the two tables are
  bisimilar from their start rows.

These are #5336's theorems transported along `read_sound`. The limits
are the same: completeness is in the opt-in quotient and for the
supported models, and every table of the fragment is `Tidy`.

## Accepted graphs

`selfLit l` and `swapLit l` are written directly in flat syntax.

* `read_selfLit`, `read_swapLit`: the reader returns `selfTable l` and
  `swapTable l`.
* `selfLit_eqv_swapLit`: the two sources are equal. Their row actions
  differ.
* `selfLit_eqv_iff`: two graphs `selfLit` have equal sources exactly when
  their labels agree.

## Rejected graphs

Each of these differs from the shape in one place, and the reader
returns `none`:

* `read_queryMiss`: the request is sent with the captured input.
* `read_carrierMiss`: an arm jumps with the block parameter and not the
  reply payload.
* `read_captureMiss`: an arm leaves with the captured input.
* `read_silentMiss`: a block jumps without a request.
* `read_entryMiss`: the entry leaves at once.
* `read_aliasMiss`: a block is behind a let.
* `read_captFlat`, `read_ctrlFlat`: the graphs of #5323 and #5330, which
  use the captured input.

## Rejection is not inequivalence

`none` says that the graph is not written in the shape of the fragment.
It is not a statement about equality of sources.

* `aliasMiss_eqv_selfLit`: the rejected graph `aliasMiss l` has the
  source of the accepted graph `selfLit l`, in default Paper.
* The rejected graphs of #5323 and #5330 have certificates
  (`captSource_bitPointed`, `ctrlSource_bitPointed`) and the
  completeness theorems of #5332.

No theorem here derives an inequality of sources from a rejection.

## Not covered

* The other near misses are only shown rejected. Nothing is proved about
  their sources.
* A reader that normalizes before matching, for example through lets.
* More than two blocks and the other shapes excluded from the fragment.
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

variable {g g' : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d d' : PollTable}

/-! ## The reader is exact -/

/-- A graph that the reader accepts is the graph of the table it returns. -/
theorem read_sound (h : read g = some d) : g = d.flat :=
  Tables.read_sound h

/-- The reader accepts the graph of every table and returns that table. -/
theorem read_flat (d : PollTable) : read d.flat = some d :=
  Tables.read_flat d

theorem read_eq_some_iff : read g = some d ↔ g = d.flat :=
  Tables.read_iff

/-! ## Sources given as flat syntax -/

/-- The region of an accepted graph is a guarded source. -/
theorem read_typed (h : read g = some d) : ValueBranches [Bit] g.erase [Bit] :=
  Tables.read_typed h

/-- The certificate at the two constant inputs, for an accepted graph. -/
theorem read_bitPointed (h : read g = some d) :
    BitPointed g.erase (fun i => some (d.label (pairBit i))) d.act (fun _ => pairIdx d.start) :=
  Tables.read_bitPointed h

/-- The region of an accepted graph is the router table of its table
entered at the start row, in the table-packing quotient. -/
theorem read_source_eqv_entered (h : read g = some d) :
    WithGuardedTablePacking.Eqv false [Bit] g.erase
      (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered (pairIdx d.start))) [Bit] :=
  Tables.read_source_entered h

/-- Two accepted graphs have equal regions at the source entry exactly
when they are valid in every supported model. -/
theorem read_complete (h : read g = some d) (h' : read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔ Valid (read_typed h).hasType (read_typed h').hasType :=
  Tables.read_complete h h'

/-- Exactly when their tables are bisimilar from their start rows. -/
theorem read_eqv_iff_bisimulation (h : read g = some d) (h' : read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔
      ∃ R : Fin 2 → Fin 2 → Prop, (∀ x y, R x y → d.label (pairBit x) = d'.label (pairBit y)) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧
        R (pairIdx d.start) (pairIdx d'.start) :=
  Tables.read_eqv_iff_bisim h h'

end PollTable

/-! ## Accepted graphs -/

theorem read_selfLit (l : Bool) : PollTable.read (selfLit l) = some (selfTable l) :=
  Tables.read_selfLit l

theorem read_swapLit (l : Bool) : PollTable.read (swapLit l) = some (swapTable l) :=
  Tables.read_swapLit l

/-- Two accepted graphs with different row actions have equal sources. -/
theorem selfLit_eqv_swapLit (l : Bool) : Eqv false [Bit] (selfLit l).erase (swapLit l).erase [Bit] :=
  Tables.selfLit_swapLit l

/-- Two graphs `selfLit` have equal sources exactly when their labels agree. -/
theorem selfLit_eqv_iff (l l' : Bool) :
    Eqv false [Bit] (selfLit l).erase (selfLit l').erase [Bit] ↔ l = l' :=
  Tables.selfLit_label l l'

/-! ## Rejected graphs -/

theorem read_queryMiss (l : Bool) : PollTable.read (queryMiss l) = none := rfl

theorem read_carrierMiss (l : Bool) : PollTable.read (carrierMiss l) = none := rfl

theorem read_captureMiss (l : Bool) : PollTable.read (captureMiss l) = none := rfl

theorem read_silentMiss (l : Bool) : PollTable.read (silentMiss l) = none := rfl

theorem read_entryMiss (l : Bool) : PollTable.read (entryMiss l) = none := rfl

theorem read_aliasMiss (l : Bool) : PollTable.read (aliasMiss l) = none := rfl

theorem read_captFlat (l : Bool) : PollTable.read (captFlat l) = none := rfl

theorem read_ctrlFlat (l₀ l₁ : Bool) : PollTable.read (ctrlFlat l₀ l₁) = none := rfl

/-! ## Rejection is not inequivalence -/

/-- A rejected graph with the source of an accepted graph, in default Paper. -/
theorem aliasMiss_eqv_selfLit (l : Bool) : Paper.Eqv [Bit] (aliasMiss l).erase (selfLit l).erase [Bit] :=
  Tables.alias_eqv l

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
