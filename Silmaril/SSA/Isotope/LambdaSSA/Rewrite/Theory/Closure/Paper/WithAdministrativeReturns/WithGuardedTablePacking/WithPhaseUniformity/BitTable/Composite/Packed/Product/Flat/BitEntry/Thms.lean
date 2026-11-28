module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Controlled.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.BitEntry

/-! # Completeness at a Bit entry from certificates at the two constant inputs

No seed and no quotient law is added. Nothing is inferred from a model
beyond the existing reflection for tidy router tables. Default Paper is
unchanged.

## The theorem

Let `s`, `s'` be guarded sources with one Bit of input and one Bit exit,
each with a certificate `BitPointed`: at each constant input the source
is a router table `Router.ofSpin` entered at a row with that input. Let
both tables be `Tidy`, the hypothesis of the existing complete fragment.

* `BitPointed.complete`: `s` and `s'` are equal at the Bit entry exactly
  when they are valid in every supported model.

The two tables may differ in size, labels and actions. Nothing asks the
labels to be the same.

## The three steps

1. **Validity to each input.** `BitPointed.atInput_eqv_of_valid`:
   validity at the entry gives equality of the two sources at each
   constant input. Validity is transported to the sources run on the Bit
   of a state (`Valid.seq_left`); the pointed observation of the
   query-aware model gives equal observations of the two tables at that
   input; the reflection of #5290 turns equal observations into equality
   of the entered tables.
2. **Bit extensionality.** `eqv_iff_atInput`: two sources on a Bit are
   equal exactly when they are equal at the two constant inputs.
   `bitInput_ext_paper` is the same assembly in **default Paper**. The
   constant inputs are built on the unit input, so they are the two
   constructors of a Bit, and a region on a Bit is the case of its two
   restrictions.
3. **Soundness** gives the converse.

## Where unit η is used

* Not in the assembly. Step 2 is default Paper; in the quotient it is
  congruence of the case.
* In the certificates. A certificate is an equation of the opt-in
  quotient. In the two instances below unit η identifies the literal
  constant of a decoded row with the constant input, and discards the
  reply on the left branch of the step equation; the packing seed is
  used once.
* Step 1 uses the existing reflection for tidy tables, which is a result
  of the opt-in quotient. This file adds no use of an opt-in rule to it.

## Instances

* `captSource_bitPointed`, `ctrlSource_bitPointed`: the certificates of
  #5327 and #5330.
* `captSource_complete_of_bitPointed`,
  `ctrlSource_complete_of_bitPointed`: their completeness theorems, now
  instances.
* `captSource_ctrlSource_complete`: across the two families, which was
  not available before: a source that returns its captured input and a
  source whose captured input chooses the request are equal exactly when
  valid in every supported model.
* `ctrlSource_same_eqv_captSource`: with one label for both values of the
  captured input the two sources are equal in **default Paper**, by
  `bitInput_ext_paper`.
* `captSource_ctrlSource_eqv_iff`: they are equal exactly when both
  labels of the second are the label of the first.

## Not covered

* Whether a flat graph has a certificate. A certificate is a hypothesis;
  nothing here finds or decides one.
* Tables that are not tidy, inputs other than one Bit, and exits other
  than one Bit in the completeness theorem.
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

variable {M M' : Nat} {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
  {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
  {x : Bool → Fin (M + 1)} {x' : Bool → Fin (M' + 1)} {D : Ty Empty} {s s' : Region signature.Instr}

/-! ## Bit extensionality -/

/-- Two sources on a Bit are equal in default Paper when they are equal
at the two constant inputs. -/
theorem bitInput_ext_paper (hs : ValueBranches [Bit] s [D]) (hs' : ValueBranches [Bit] s' [D])
    (e : ∀ q, Paper.Eqv [Ty.unit] (atInput q s) (atInput q s') [D]) : Paper.Eqv [Bit] s s' [D] :=
  (Paper.TypeCategory.ofRegion_eq_iff hs hs').mp
    (Tables.bit_ext_paper hs hs' fun q => (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (e q))

/-- Two sources on a Bit are equal exactly when they are equal at the two
constant inputs. -/
theorem eqv_iff_atInput (hs : ValueBranches [Bit] s [D]) (hs' : ValueBranches [Bit] s' [D]) :
    Eqv false [Bit] s s' [D] ↔ ∀ q, Eqv false [Ty.unit] (atInput q s) (atInput q s') [D] :=
  Tables.eqv_iff_inputs hs hs'

/-! ## Certificates -/

/-- A certificate at the two constant inputs is a pointed representation
of the source run on the Bit of a state. -/
theorem BitPointed.iff_spinPointed (hs : ValueBranches [Bit] s [Bit]) :
    BitPointed s label act x ↔ SpinPointed (seqRegion (unpackExits [Bit]) s) label act x :=
  Tables.bitPointed_iff_spin hs

/-- A table with no silent row is tidy. -/
theorem Tidy.of_labelled (h : ∀ j, label j ≠ none) : Tidy label act :=
  Tables.tidy_of_labelled h

/-- Validity at the Bit entry gives equality at each constant input. -/
theorem BitPointed.atInput_eqv_of_valid (ht : Tidy label act) (ht' : Tidy label' act')
    (hs : ValueBranches [Bit] s [Bit]) (hs' : ValueBranches [Bit] s' [Bit])
    (hp : BitPointed s label act x) (hp' : BitPointed s' label' act' x')
    (v : Valid hs.hasType hs'.hasType) (q : Bool) :
    Eqv false [Ty.unit] (atInput q s) (atInput q s') [Bit] :=
  Tables.spec_of_valid ht ht' hs hs' hp hp' v q

/-- Two sources with certificates in tidy tables are equal at the Bit
entry exactly when they are valid in every supported model. -/
theorem BitPointed.complete (ht : Tidy label act) (ht' : Tidy label' act')
    (hs : ValueBranches [Bit] s [Bit]) (hs' : ValueBranches [Bit] s' [Bit])
    (hp : BitPointed s label act x) (hp' : BitPointed s' label' act' x') :
    Eqv false [Bit] s s' [Bit] ↔ Valid hs.hasType hs'.hasType :=
  Tables.bit_source_complete ht ht' hs hs' hp hp'

/-! ## Instances -/

theorem captSource_bitPointed (l : Bool) : BitPointed (captSource l) (fun _ => some l) captAct pairIdx :=
  Tables.capt_bitPointed l

theorem ctrlSource_bitPointed (l₀ l₁ : Bool) :
    BitPointed (ctrlSource l₀ l₁) (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct pairIdx :=
  Tables.ctrl_bitPointed l₀ l₁

/-- #5327's completeness theorem, as an instance. -/
theorem captSource_complete_of_bitPointed (l l' : Bool) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] ↔
      Valid (captSource_typed l).hasType (captSource_typed l').hasType :=
  Tables.capt_complete_inst l l'

/-- #5330's completeness theorem, as an instance. -/
theorem ctrlSource_complete_of_bitPointed (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlSource l₀' l₁') [Bit] ↔
      Valid (ctrlSource_typed l₀ l₁).hasType (ctrlSource_typed l₀' l₁').hasType :=
  Tables.ctrl_complete_inst l₀ l₁ l₀' l₁'

/-- Across the two families. -/
theorem captSource_ctrlSource_complete (l l₀ l₁ : Bool) :
    Eqv false [Bit] (captSource l) (ctrlSource l₀ l₁) [Bit] ↔
      Valid (captSource_typed l).hasType (ctrlSource_typed l₀ l₁).hasType :=
  Tables.capt_ctrl_complete l l₀ l₁

/-- With one label for both values of the captured input, the source
whose captured input chooses the request is the source that returns its
captured input, in default Paper. -/
theorem ctrlSource_same_eqv_captSource (l : Bool) :
    Paper.Eqv [Bit] (ctrlSource l l) (captSource l) [Bit] :=
  Tables.ctrl_same_capt l

/-- They are equal exactly when both labels of the second are the label
of the first. -/
theorem captSource_ctrlSource_eqv_iff (l l₀ l₁ : Bool) :
    Eqv false [Bit] (captSource l) (ctrlSource l₀ l₁) [Bit] ↔ l₀ = l ∧ l₁ = l :=
  Tables.capt_ctrl_eqv_iff l l₀ l₁

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
