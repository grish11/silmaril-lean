module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Written.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PackedSource

/-! # Packed dispatcher loops at their packed state, and source loops

No seed and no quotient law is added. No equality of the quotient is
inferred from a model.

## Transport of validity

`Valid.seq_left`: two guarded regions that are valid in every supported
model stay valid after a guarded region is run before them. It holds for
every supported model by functoriality of its denotation; no model is
fixed.

## Packed loops on their packed state

`Router.loop t` is the packed loop on `States K`, a tagged sum with one
Bit for each row. It is the state of the whole dispatcher, not of one
entry.

* `Router.loop_arrow_dispatch`: a packed loop is the dispatcher of its
  entered loops, in default Paper.
* `Router.loop_eqv_iff_entries`: two packed loops are equal exactly when
  they are equal at every original entry. This is the entry-preserving
  factorization at the packed state.
* `Router.loop_complete`: two packed loops of the same size are equal on
  their packed state exactly when they are valid in every supported
  model. The converse transports validity to each entry with
  `Valid.seq_left` and uses `Router.complete`.

## Source loops that factor through a packed loop

`Factors.complete`: let `src` and `src'` be loops on any state type `S`,
with one encoding `enc : S → States K` and decoding `dec : States K → S`
such that `Retracts S enc dec`, and with `Factors dec src t` and
`Factors dec src' t'`. Then `src` and `src'` are equal exactly when they
are valid in every supported model.

These two hypotheses are the exact factorization that `Router.complete`
needs from a source dispatcher: a finite decoding of its state into rows
that each carry one Bit, with a section, and the equation that the source
on a decoded state is the packed loop.

## Regression: two tagged live Bits

On `States 1`, the packed state of two rows:

* `letStash_loop_eqv`: the written table with lets and its mixed table
  have equal packed loops.
* `letStash_loop_ne`: a changed blind query is distinguished on the
  packed state.

## What is not covered, and why

The one-Bit interface is the type `States K`: finitely many tags, each
with exactly one Bit, and no other component. Two source shapes do not
have that type.

* The packed readback of a source CFG, `packedReadbackRep`, the right
  side of the packing seed. Its loop state is
  `product X (packedExitType (List.ofFn R))`: the capture `X` paired with
  the tagged sum of the block parameters `R i`, with rows through the
  distributor. To use `Factors.complete` one needs an encoding and a
  decoding between that product and `States K` with `Retracts`, which
  needs each `product X (R i)` to be a finite sum of Bits, and `Factors`
  for the readback loop, which needs each ordered row to be a router row.
  Neither is constructed here.
* A state with two live Bits as a product, `product Bit Bit`. It is a sum
  of two Bits only through the distributor and the product laws, and a
  loop on it is related to a packed loop by transport of iteration along
  that isomorphism. Neither is constructed here.

So no source CFG and no product state is covered. Nothing is claimed for
packed dispatchers in general, and no completeness is claimed for default
Paper.
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


variable {K : Nat}

/-! ## Transport of validity -/

/-- Valid regions stay valid after a guarded region is run before them. -/
theorem Valid.seq_left {X Y Z : Ty Empty} {g r s : Region signature.Instr} (hg : ValueBranches [X] g [Y])
    (hr : ValueBranches [Y] r [Z]) (hs : ValueBranches [Y] s [Z]) (v : Valid hr.hasType hs.hasType) :
    Valid (seqRegion_typed hg hr).hasType (seqRegion_typed hg hs).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Valid.seq hg hr hs
    v

/-! ## Packed loops on their packed state -/

/-- A packed loop is the dispatcher of its entered loops, in default Paper. -/
theorem Router.loop_arrow_dispatch (t : Router K) :
    ofRegion t.loop_typed = ofRegion (dispatch_typed K fun i => t.entered_typed i) :=
  Tables.loop_as_dispatch t.rows_typed

/-- Two packed loops are equal exactly when they are equal at every
original entry. -/
theorem Router.loop_eqv_iff_entries (t t' : Router K) :
    Eqv false [States K] t.loop t'.loop [Bit] ↔ ∀ i, Eqv false [State] (t.entered i) (t'.entered i) [Bit] :=
  Tables.loop_eqv_iff_entries t t'

/-- Two packed loops are equal on their packed state exactly when they
are valid in every supported model. -/
theorem Router.loop_complete (t t' : Router K) :
    Eqv false [States K] t.loop t'.loop [Bit] ↔ Valid t.loop_typed.hasType t'.loop_typed.hasType :=
  Tables.loop_complete t t'

/-! ## Source loops that factor through a packed loop -/

/-- Two source loops that factor through packed loops along one decoding
with a section are equal exactly when they are valid in every supported
model. -/
theorem Factors.complete {S : Ty Empty} {enc dec src src' : Region signature.Instr} {t t' : Router K}
    (hf : Factors dec src t) (hf' : Factors dec src' t') (ret : Retracts S enc dec)
    (he : ValueBranches [S] enc [States K]) (hd : ValueBranches [States K] dec [S])
    (hs : ValueBranches [S] src [Bit]) (hs' : ValueBranches [S] src' [Bit]) :
    Eqv false [S] src src' [Bit] ↔ Valid hs.hasType hs'.hasType :=
  Tables.factored_complete he hd hs hs' ret t t' hf hf'

/-! ## Regression: two tagged live Bits -/

/-- The written table with lets and its mixed table have equal packed
loops on the packed state of two rows. -/
theorem letStash_loop_eqv (l₁ l₂ s n f : Bool) :
    Eqv false [States 1] (letStash l₁ l₂ s n f).loop (mixWritten (stashRow l₁ l₂ s) (stashAct n f)).loop
      [Bit] :=
  Tables.letStash_loop_eqv l₁ l₂ s n f

/-- A changed blind query is distinguished on the packed state. -/
theorem letStash_loop_ne (l₁ l₂ n f n' f' : Bool) :
    ¬ Eqv false [States 1] (letStash l₁ l₂ false n f).loop (letStash l₁ l₂ true n' f').loop [Bit] :=
  Tables.letStash_loop_ne l₁ l₂ n f n' f'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
