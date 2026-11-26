module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement.Defs
public import Silmaril.Semantics.Elgot.Thms

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

open CategoryTheory Silmaril.Elgot Silmaril.Logic.Institution
open Silmaril.SSA.LambdaRTL.Institution (LawfulModel)
open Comparison

variable {V K F F' α : Type} [DecidableEq V] [DecidableEq K]

theorem rtlSat_map_iff (h : F → F') (model : PairModel F' Part α) (lhs rhs : RTLClass V K F Part α) :
    rtlSat model (rtlMapClass h lhs) (rtlMapClass h rhs) ↔ rtlSat (LawfulModel.reduct h model) lhs rhs :=
  rtlRelSat_map_iff (· ≤ ·) h model lhs rhs

theorem ssaSat_map_iff (h : F → F') (model : PairModel F' Part α) (lhs rhs : SSAClass V K F Part α) :
    ssaSat model (ssaMapClass h lhs) (ssaMapClass h rhs) ↔ ssaSat (LawfulModel.reduct h model) lhs rhs :=
  ssaRelSat_map_iff (· ≤ ·) h model lhs rhs

theorem rtlRefines_map (h : F → F') {lhs rhs : RTLClass V K F Part α}
    (refines : rtlRefines lhs rhs) : rtlRefines (rtlMapClass h lhs) (rtlMapClass h rhs) :=
  fun model => (rtlSat_map_iff h model lhs rhs).mpr (refines (LawfulModel.reduct h model))

theorem ssaRefines_map (h : F → F') {lhs rhs : SSAClass V K F Part α}
    (refines : ssaRefines lhs rhs) : ssaRefines (ssaMapClass h lhs) (ssaMapClass h rhs) :=
  fun model => (ssaSat_map_iff h model lhs rhs).mpr (refines (LawfulModel.reduct h model))

theorem ssaSat_version_iff (model : PairModel F Part α) (lhs rhs : RTLClass V K F Part α) :
    ssaSat model (versionClass lhs) (versionClass rhs) ↔ rtlSat model lhs rhs :=
  ssaRelSat_version_iff (· ≤ ·) model lhs rhs

/-- Versioning preserves and reflects the oriented order in all models. -/
theorem version_refines_iff (lhs rhs : RTLClass V K F Part α) :
    ssaRefines (versionClass lhs) (versionClass rhs) ↔ rtlRefines lhs rhs :=
  forall_congr' fun model => ssaSat_version_iff model lhs rhs

theorem rtlSat_deversion_iff [Infinite V] (model : PairModel F Part α)
    (lhs rhs : SSAClass V K F Part α) :
    rtlSat model (deversionClass lhs) (deversionClass rhs) ↔ ssaSat model lhs rhs :=
  rtlRelSat_deversion_iff (· ≤ ·) model lhs rhs

/-- Deversioning preserves and reflects the oriented order in all models. -/
theorem deversion_refines_iff [Infinite V] (lhs rhs : SSAClass V K F Part α) :
    rtlRefines (deversionClass lhs) (deversionClass rhs) ↔ ssaRefines lhs rhs :=
  forall_congr' fun model => rtlSat_deversion_iff model lhs rhs

/-- Mutual result inclusion gives equality of mutable observational classes. -/
@[instance_reducible]
def rtlOrder : PartialOrder (RTLClass V K F Part α) where
  le := rtlRefines
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ forward next model store := le_trans (forward model store) (next model store)
  le_antisymm lhs rhs := Quotient.inductionOn₂ lhs rhs fun _ _ forward backward =>
    Quotient.sound fun model store => le_antisymm (forward model store) (backward model store)

/-- Mutual result inclusion gives equality of lexical observational classes. -/
@[instance_reducible]
def ssaOrder : PartialOrder (SSAClass V K F Part α) where
  le := ssaRefines
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ forward next model store := le_trans (forward model store) (next model store)
  le_antisymm lhs rhs := Quotient.inductionOn₂ lhs rhs fun _ _ forward backward =>
    Quotient.sound fun model store => le_antisymm (forward model store) (backward model store)

/-- Versioning and deversioning identify the two orders on program classes. -/
noncomputable def classOrderIso [Infinite V] :
    @OrderIso (RTLClass V K F Part α) (SSAClass V K F Part α) rtlOrder.toLE ssaOrder.toLE where
  toEquiv := classEquiv
  map_rel_iff' := version_refines_iff _ _

variable (V K α)

/-- The refinement institutions are naturally isomorphic over the shared alphabet
category, with identity on models and the comparison of classes on both operands. -/
noncomputable def comparisonIso [Infinite V] : (rtl V K α).I ≅ (ssa V K α).I :=
  relationComparisonIso V K Part α (· ≤ ·)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement
