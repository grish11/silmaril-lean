module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptStep

/-! # A two-block cyclic flat source whose header uses the captured input

No seed and no quotient law is added. Nothing is inferred from a model.
Default Paper is unchanged.

## The source

`captFlat l` is a scoped flat graph with two blocks, one exit and one
captured input `c`. The header sends the request `l` with its parameter;
on the left reply it leaves with the captured input `c`; on the right
reply `r` it jumps to the back-edge block with `r`, which jumps back to
the header. The captured input reaches the exit, so the header row
depends on it. `captFlat_typed` types the graph in the flat judgment.

The graph is not obtained from a named table: the existing elaborator of
named tables gives a block only its parameter.

## The route

1. **Seed.** `captSource_readback`: the source equals its packed
   readback, by the existing table-packing seed.
2. **The captured input as a factor.** `twoRows_keep`: a two-row
   dispatcher whose rows are capture-free rows whiskered by the captured
   input and followed by one tail `K` iterates as the whiskered
   capture-free loop followed by the return map of the tail. Default
   Paper: distribution over the tags, iteration strength, naturality. It
   is stated for any tail whose arrow is the inverse comparison followed
   by a map on the return side. #5314's `twoRows_iterate` is the
   analogous statement for the tail that drops the input.
3. **This source.** Its rows have the tail `keepCase`, which keeps the
   captured input in the state and returns it. `captReadback_keeps`: the
   readback duplicates the input, runs the capture-free poll loop on one
   copy while keeping the other, and returns the kept copy. The
   back-edge block is eliminated by the Bekič law, as in #5314.
4. **An explicit state factor.** `captReadback_eqv_loop`: the readback is
   `captLoop l`, the loop of `captBody l` on the pair of captured input
   and header parameter, entered with the input in both places. Default
   Paper.

`captSource_eqv_loop`: so the source equals `captLoop l` at the source
entry, in the table-packing quotient.

## The router table and completeness

`captRouter l` is the two-row router table of the loop: the row is the
captured input and the carried Bit is the header parameter.

* `captBody_step`: the step `captBody l`, conjugated by the encoding of
  pairs, is the dispatcher step of `captRouter l`. The proof follows
  #5306's for `pairBody`: packed row extensionality; product β with the
  captured Bit as the constant of the row; congruence under the request.
  On the right reply the encoding at a constant first Bit and the case of
  a Bit on its constructors suffice, in default Paper. On the left reply
  unit η discards the reply. Unit η is the only opt-in rule used.
* `captLoop_factors`, `captLoop_complete`: the loop of `captBody`
  factors through the packed loop of the table, and two such loops are
  equal at the product-state entry exactly when valid in every supported
  model.

At the source entry the loop is entered only at pairs with equal
components, so the iff is proved for this family directly, not from an
abstract principle about diagonal states.

* `captSource_pointed`: at each constant input `q` the source is the
  router table entered at the row of `q`, carrying `q`. It uses the
  factoring above and unit η for the constant of the row.
* `captSource_label_of_valid`: validity at the source entry determines
  the request label. In the query-aware model of #5290 the first request
  of the table at that state shows its label.
* `captSource_complete`: two sources are equal at the source entry
  exactly when they are valid in every supported model. Equal labels give
  the same source.
* `captSource_eqv_iff`: they are equal exactly when their requests have
  the same label.

These use the opt-in quotient: the packing seed, unit η and phase
uniformity.

The `_of` forms with the step equation as a hypothesis remain.

## Not covered

* The reduction without the table-packing seed (#5316 and #5319 show it
  is not available for the capture-free two-block source in the
  quotients below).
* A row whose use of the captured input is not of the lifted form with
  one common tail: for example a request whose query is the captured
  input.
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
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (iterate sumIso whiskerLeft tensorObj
  leftCoproductComparisonIso)

/-! ## The source -/

/-- The flat graph is typed in the flat judgment: both blocks receive a
Bit, the exit a Bit, and the captured input is a Bit. -/
theorem captFlat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit)
      (captFlat l) :=
  Tables.capt_flat_typed l

/-! ## The captured input as a factor, in default Paper -/

/-- A dispatcher of two rows that are capture-free rows whiskered by the
captured input and followed by a tail `K` iterates as the whiskered
capture-free loop followed by `g`, when the arrow of `K` is the inverse
comparison followed by `g` on the return side. -/
theorem twoRows_keep {X A₀ A₁ D E : Ty Empty} {ρ₀ ρ₁ dR β₀ β₁ K : Region signature.Instr}
    (hK : ValueBranches
      [Silmaril.product X (Silmaril.coprod E (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))] K
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (g : tensorObj (ofType (Φ := signature.Instr) X) (ofType E) ⟶ ofType (Φ := signature.Instr) D)
    (hKg : ofRegion hK ≫ (sumIso (Φ := signature.Instr) D
        (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))).hom =
      whiskerLeft (ofType (Φ := signature.Instr) X) (sumIso (Φ := signature.Instr) E
          (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))).hom ≫
        ((leftCoproductComparisonIso (ofType (Φ := signature.Instr) X) (ofType E)
            (ofType (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))).inv ≫
          coprod.map g (𝟙 (tensorObj (ofType (Φ := signature.Instr) X)
            (ofType (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))))))
    (hρ₀ : ValueBranches [Silmaril.product X A₀] ρ₀
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (hρ₁ : ValueBranches [Silmaril.product X A₁] ρ₁
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (hd : ValueBranches [Silmaril.empty] dR
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))])
    (hβ₀ : ValueBranches [A₀] β₀
      [Silmaril.coprod E (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))])
    (hβ₁ : ValueBranches [A₁] β₁
      [Silmaril.coprod E (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))])
    (e₀ : ofRegion hρ₀ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₀) hK))
    (e₁ : ofRegion hρ₁ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₁) hK))
    (hdisp : ValueBranches [Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))]
      (twoRows ρ₀ ρ₁ dR)
      [Silmaril.coprod D (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))]) :
    iterate (ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D
        (Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)))).hom) =
      whiskerLeft (ofType (Φ := signature.Instr) X) (iterate (freeStep hβ₀ hβ₁)) ≫ g :=
  Tables.two_row_keep hK g hKg hρ₀ hρ₁ hd hβ₀ hβ₁ e₀ e₁ hdisp

/-- The packed readback duplicates the input, runs the capture-free poll
loop on one copy while keeping the other, and returns the kept copy. -/
theorem captReadback_keeps (l : Bool) :
    ofRegion (captReadback l).property =
      ofRegion dupEntry_typed ≫
        (whiskerLeft (ofType (Φ := signature.Instr) Bit)
            (iterate (ofRegion (pollBody_typed l) ≫ (sumIso (Φ := signature.Instr) Bit Bit).hom)) ≫
          ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit))) :=
  Tables.capt_readback_arrow l

/-- The packed readback is the loop on the pair of captured input and
header parameter, entered with the input in both places. Default Paper. -/
theorem captReadback_eqv_loop (l : Bool) : Paper.Eqv [Bit] (captReadback l).val (captLoop l) [Bit] :=
  Tables.capt_readback_loop l

/-! ## The source and the loop on the pair -/

/-- The table-packing seed at the source. -/
theorem captSource_readback (l : Bool) :
    WithGuardedTablePacking.Eqv false [Bit] (captSource l) (captReadback l).val [Bit] :=
  Tables.capt_source_readback l

/-- The source is the loop on the pair of captured input and parameter,
at the source entry, in the table-packing quotient. -/
theorem captSource_eqv_loop (l : Bool) :
    WithGuardedTablePacking.Eqv false [Bit] (captSource l) (captLoop l) [Bit] :=
  Tables.capt_source_loop l

/-! ## The router table, conditional on the open step equation -/

/-- If the conjugated step is the dispatcher step, the loop on the pair
factors through the packed loop of the router table. -/
theorem captLoop_factors_of (l : Bool) (h : Task.captStep l) :
    Factors pairDec (loopRegion Pair (captBody l)) (captRouter l) :=
  Tables.capt_factors_of l h

/-- If the conjugated steps are the dispatcher steps, two loops on the
pair are equal at the product-state entry exactly when they are valid in
every supported model. -/
theorem captLoop_complete_of (l l' : Bool) (h : Task.captStep l) (h' : Task.captStep l') :
    Eqv false [Pair] (loopRegion Pair (captBody l)) (loopRegion Pair (captBody l')) [Bit] ↔
      Valid (loopRegion_typed (captBody_typed l)).hasType (loopRegion_typed (captBody_typed l')).hasType :=
  Tables.capt_complete_of l l' h h'

/-- Two sources are equal at the source entry when their loops on the
pair are equal at the product-state entry. -/
theorem captSource_eqv_of_loops (l l' : Bool)
    (e : Eqv false [Pair] (loopRegion Pair (captBody l)) (loopRegion Pair (captBody l')) [Bit]) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] :=
  Tables.capt_source_of_loops l l' e

/-! ## The router table and completeness -/

/-- The step that keeps the captured input, conjugated by the encoding of
pairs, is the dispatcher step of its router table. -/
theorem captBody_step (l : Bool) : Task.captStep l :=
  Tables.capt_step l

/-- The loop on the pair factors through the packed loop of its router table. -/
theorem captLoop_factors (l : Bool) : Factors pairDec (loopRegion Pair (captBody l)) (captRouter l) :=
  captLoop_factors_of l (captBody_step l)

/-- Two loops on the pair are equal at the product-state entry exactly
when they are valid in every supported model. -/
theorem captLoop_complete (l l' : Bool) :
    Eqv false [Pair] (loopRegion Pair (captBody l)) (loopRegion Pair (captBody l')) [Bit] ↔
      Valid (loopRegion_typed (captBody_typed l)).hasType (loopRegion_typed (captBody_typed l')).hasType :=
  captLoop_complete_of l l' (captBody_step l) (captBody_step l')

/-- At each constant input the source is the router table entered at the
row of that constant, carrying that constant. -/
theorem captSource_pointed (l : Bool) :
    SpinPointed (seqRegion (unpackExits [Bit]) (captSource l)) (fun _ => some l) captAct pairIdx :=
  Tables.capt_pointed l

/-- Validity at the source entry determines the request label. -/
theorem captSource_label_of_valid (l l' : Bool)
    (v : Valid (captSource_typed l).hasType (captSource_typed l').hasType) : l = l' :=
  Tables.capt_label_of_valid l l' v

/-- Two sources are equal at the source entry exactly when they are
valid in every supported model. -/
theorem captSource_complete (l l' : Bool) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] ↔
      Valid (captSource_typed l).hasType (captSource_typed l').hasType :=
  Tables.capt_source_complete l l'

/-- They are equal exactly when their requests have the same label. -/
theorem captSource_eqv_iff (l l' : Bool) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] ↔ l = l' :=
  Tables.capt_source_eqv_iff l l'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
