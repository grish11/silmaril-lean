module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ControlledSource

/-! # Completeness at a Bit entry from certificates at the two constant inputs -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.TypeCategory (iterate_roll)
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CfgEta.TypeCategory (productSndBranches whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.TypeCategory (whiskerLeft whiskerLeft_comp whiskerLeft_id whiskerLeft_ofRegion whiskerLeftFunctor
  tensorObj leftCoproductComparisonIso leftCoproductComparisonIso_hom leftCoproductComparisonIso_inv
  leftCoproductDistributor)
open Paper.TypeCategory.Projection (productSnd iterate_projected_whiskerLeft)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep dispatcherRep orderedRow emptyDispatchRep)
open Paper.TypeCategory (sumInl sumInr blockRoute blockStep iterate_blockStep iterate_fixpoint)
open Paper.TypeCategory (whiskerLeft_iterate iterate_naturality)

section BitEntry

variable {M M' : Nat} {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
  {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
  {x : Bool → Fin (M + 1)} {x' : Bool → Fin (M' + 1)} {D : Ty Empty} {s s' : Region signature.Instr}

/-! ## A Bit input is one of its two constants -/

/-- Two sources on a Bit are equal in default Paper when they are equal
at the two constant inputs. No unit η: a Bit is the case of its two
constructors on the unit input. -/
theorem bit_ext_paper (hs : ValueBranches [Bit] s [D]) (hs' : ValueBranches [Bit] s' [D])
    (e : ∀ q, ofRegion (atInput_typed q hs) = ofRegion (atInput_typed q hs')) : ofRegion hs = ofRegion hs' :=
  (bit_eta hs).trans
    (((coprod_desc_ofRegion (seqValueBranches inlU_typed hs) (seqValueBranches inrU_typed hs)).symm.trans
      ((congrArg₂ (fun u v => (sumIso (Φ := signature.Instr) U U).hom ≫ coprod.desc u v) (e false) (e true)).trans
        (coprod_desc_ofRegion (seqValueBranches inlU_typed hs') (seqValueBranches inrU_typed hs')))).trans
      (bit_eta hs').symm)

/-- The same in the quotient, by congruence of the case. -/
theorem bit_ext_q (hs : ValueBranches [Bit] s [D]) (hs' : ValueBranches [Bit] s' [D])
    (e : ∀ q, QLit (atInput_typed q hs) = QLit (atInput_typed q hs')) : QLit hs = QLit hs' :=
  (congrArg (π).map (bit_eta hs)).trans
    ((q_case_congr (seqValueBranches inlU_typed hs) (seqValueBranches inrU_typed hs)
      (seqValueBranches inlU_typed hs') (seqValueBranches inrU_typed hs') (e false) (e true)).trans
      (congrArg (π).map (bit_eta hs')).symm)

/-- Two sources on a Bit are equal exactly when they are equal at the two
constant inputs. -/
theorem eqv_iff_inputs (hs : ValueBranches [Bit] s [D]) (hs' : ValueBranches [Bit] s' [D]) :
    Eqv false [Bit] s s' [D] ↔ ∀ q, Eqv false [U] (atInput q s) (atInput q s') [D] :=
  ⟨fun e q => (Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs) (atInput_typed q hs')).1
      ((q_comp (bitU_typed q) hs).trans
        ((congrArg (QLit (bitU_typed q) ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N hs hs').2 e)).trans (q_comp (bitU_typed q) hs').symm)),
    fun e => (Paper.Extension.Singleton.ofRegion_eq_iff N hs hs').1
      (bit_ext_q hs hs' fun q =>
        (Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs) (atInput_typed q hs')).2 (e q))⟩

/-! ## Certificates -/

/-- A certificate at the two constant inputs is a pointed representation
of the source run on the Bit of a state. Default Paper relates the two. -/
theorem bitPointed_iff_spin (hs : ValueBranches [Bit] s [Bit]) :
    BitPointed s label act x ↔ SpinPointed (seqRegion (unpackExits [Bit]) s) label act x :=
  ⟨fun e q => (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (seqRegion_typed unpack_typed hs))
      (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))).1
      ((const_state hs q).trans
        ((Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs)
          (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))).2 (e q))),
    fun e q => (Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs)
      (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))).1
      ((const_state hs q).symm.trans
        ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (seqRegion_typed unpack_typed hs))
          (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))).2 (e q)))⟩

/-- A table with no silent row is tidy. -/
theorem tidy_of_labelled (h : ∀ j, label j ≠ none) : Tidy label act :=
  fun _ _ _ _ _ j _ _ hn => absurd hn (h j)

section Reflect

variable (ht : Tidy label act) (ht' : Tidy label' act')

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
include ht ht' in
/-- Validity at the Bit entry gives equality at each constant input: the
pointed observation of the query-aware model, and the reflection of
observations for tidy tables. -/
theorem spec_of_valid (hs : ValueBranches [Bit] s [Bit]) (hs' : ValueBranches [Bit] s' [Bit])
    (hp : BitPointed s label act x) (hp' : BitPointed s' label' act' x')
    (v : Valid hs.hasType hs'.hasType) (q : Bool) :
    Eqv false [U] (atInput q s) (atInput q s') [Bit] := by
  have vS : Valid (seqRegion_typed unpack_typed hs).hasType (seqRegion_typed unpack_typed hs').hasType :=
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Valid.seq
      unpack_typed hs hs' v
  have obs := TableModel.query_pointed_obs (seqRegion_typed unpack_typed hs) (seqRegion_typed unpack_typed hs')
    ((bitPointed_iff_spin hs).1 hp) ((bitPointed_iff_spin hs').1 hp') vS q
  have rows := TableModel.query_eqv_of_obs label act label' act' ht ht' (x q) (x' q) q obs
  have ce : QLit (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q))) =
      QLit (constEntry_typed q ((Router.ofSpin label' act').entered_typed (x' q))) :=
    (q_comp (const_typed q) ((Router.ofSpin label act).entered_typed (x q))).trans
      ((congrArg (QLit (const_typed q) ≫ ·)
        ((Paper.Extension.Singleton.ofRegion_eq_iff N ((Router.ofSpin label act).entered_typed (x q))
          ((Router.ofSpin label' act').entered_typed (x' q))).2 rows)).trans
        (q_comp (const_typed q) ((Router.ofSpin label' act').entered_typed (x' q))).symm)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs) (atInput_typed q hs')).1
    (((Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs)
      (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))).2 (hp q)).trans
      (ce.trans ((Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q hs')
        (constEntry_typed q ((Router.ofSpin label' act').entered_typed (x' q)))).2 (hp' q)).symm))

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
include ht ht' in
/-- Two sources with certificates in tidy tables are equal at the Bit
entry exactly when they are valid in every supported model. -/
theorem bit_source_complete (hs : ValueBranches [Bit] s [Bit]) (hs' : ValueBranches [Bit] s' [Bit])
    (hp : BitPointed s label act x) (hp' : BitPointed s' label' act' x') :
    Eqv false [Bit] s s' [Bit] ↔ Valid hs.hasType hs'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => (eqv_iff_inputs hs hs').2 (spec_of_valid ht ht' hs hs' hp hp' v)⟩

end Reflect

end BitEntry

/-! ## The two families -/

theorem capt_bitPointed (l : Bool) : BitPointed (captSource l) (fun _ => some l) captAct pairIdx :=
  (bitPointed_iff_spin (captSource_typed l)).2 (capt_pointed l)

theorem ctrl_bitPointed (l₀ l₁ : Bool) :
    BitPointed (ctrlSource l₀ l₁) (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct pairIdx :=
  (bitPointed_iff_spin (ctrlSource_typed l₀ l₁)).2 (ctrl_pointed l₀ l₁)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- #5327's completeness, as an instance. -/
theorem capt_complete_inst (l l' : Bool) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] ↔
      Valid (captSource_typed l).hasType (captSource_typed l').hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) (captSource_typed l) (captSource_typed l')
    (capt_bitPointed l) (capt_bitPointed l')

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- #5330's completeness, as an instance. -/
theorem ctrl_complete_inst (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlSource l₀' l₁') [Bit] ↔
      Valid (ctrlSource_typed l₀ l₁).hasType (ctrlSource_typed l₀' l₁').hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) (ctrlSource_typed l₀ l₁) (ctrlSource_typed l₀' l₁')
    (ctrl_bitPointed l₀ l₁) (ctrl_bitPointed l₀' l₁')

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Across the two families: a source that returns its captured input and
a source whose captured input chooses the request are equal at the source
entry exactly when they are valid in every supported model. -/
theorem capt_ctrl_complete (l l₀ l₁ : Bool) :
    Eqv false [Bit] (captSource l) (ctrlSource l₀ l₁) [Bit] ↔
      Valid (captSource_typed l).hasType (ctrlSource_typed l₀ l₁).hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) (captSource_typed l) (ctrlSource_typed l₀ l₁)
    (capt_bitPointed l) (ctrl_bitPointed l₀ l₁)

/-- With the same label for both values of the captured input, the source
whose captured input chooses the request is the source that returns its
captured input, in default Paper: they agree at the two constant inputs. -/
theorem ctrl_same_capt (l : Bool) : Paper.Eqv [Bit] (ctrlSource l l) (captSource l) [Bit] :=
  (Paper.TypeCategory.ofRegion_eq_iff (ctrlSource_typed l l) (captSource_typed l)).mp
    (bit_ext_paper (ctrlSource_typed l l) (captSource_typed l) fun q => by
      cases q
      · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (ctrl_const l l false)
      · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (ctrl_const l l true))

/-- They are equal exactly when both labels of the second are the label
of the first. -/
theorem capt_ctrl_eqv_iff (l l₀ l₁ : Bool) :
    Eqv false [Bit] (captSource l) (ctrlSource l₀ l₁) [Bit] ↔ l₀ = l ∧ l₁ = l :=
  ⟨fun e =>
      have h := (ctrl_source_eqv_iff l l l₀ l₁).1 ((Paper.Extension.Eqv.paper (ctrl_same_capt l)).trans e)
      ⟨h.1.symm, h.2.symm⟩,
    by
      rintro ⟨rfl, rfl⟩
      exact (Paper.Extension.Eqv.paper (ctrl_same_capt _)).symm⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
