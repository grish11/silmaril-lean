module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.ExitPacking.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithAdministrativeReturns.WithGuardedTablePacking
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff ofRegion_packExits_eq_iff)
open Semantics.Categorical

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem valid_of_eqv {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Eqv pe Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) : Valid hr hs :=
  fun J _ _ M _ _ shared => e.sound pe J M shared hr hs

theorem Valid.symm {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {hr : HasType Γ r L}
    {hs : HasType Γ s L} (h : Valid hr hs) : Valid hs hr :=
  fun J _ _ M _ _ shared => (h J M shared).symm

theorem Valid.trans {Γ : VCtx τ} {L : LCtx τ} {r s t : Region Φ} {hr : HasType Γ r L}
    {hs : HasType Γ s L} {ht : HasType Γ t L} (h : Valid hr hs) (k : Valid hs ht) : Valid hr ht :=
  fun J _ _ M _ _ shared => (h J M shared).trans (k J M shared)

/-- The categorical exit packing is invertible, so tagging the exits
neither adds nor removes model equalities. -/
theorem valid_packExits_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Valid hr.packExits.hasType hs.packExits.hasType ↔ Valid hr.hasType hs.hasType := by
  constructor
  · intro h V C _ _ _ _ _ _ _ _ _ _ _ _ J _ _ M _ _ shared
    have eq := h J M shared
    rw [denoteRegion_packExits_valueBranches J M shared hr,
      denoteRegion_packExits_valueBranches J M shared hs] at eq
    have cancel : J.map (packLabelExit M L) ≫ J.map (unpackLabelExit M L) = 𝟙 _ := by
      rw [← J.map_comp, packLabelExit_unpackLabelExit, J.map_id]
    simpa only [Category.assoc, cancel, Category.comp_id] using
      congrArg (· ≫ J.map (unpackLabelExit M L)) eq
  · intro h V C _ _ _ _ _ _ _ _ _ _ _ _ J _ _ M _ _ shared
    rw [denoteRegion_packExits_valueBranches J M shared hr,
      denoteRegion_packExits_valueBranches J M shared hs, h J M shared]

variable {n m : Nat} (R : Fin (n + 1) → τ) (S : Fin (m + 1) → τ) {X : τ} {L : LCtx τ}
  {e e' : Region Φ} {blocks : Fin (n + 1) → Region Φ} {blocks' : Fin (m + 1) → Region Φ}
  (he : ValueBranches [X] e (List.ofFn R ++ L))
  (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L))
  (he' : ValueBranches [X] e' (List.ofFn S ++ L))
  (hb' : ∀ i, ValueBranches [S i, X] (blocks' i) (List.ofFn S ++ L))

/-- The exit-tagged table and its packed representative, as one equation. -/
theorem packExits_eqv_packed :
    Eqv pe [X] (Region.cfg e (n + 1) blocks).packExits
      (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).val [packedExitType L] :=
  pack pe R (tagExits_entry R he) (tagExits_row R hb)

theorem table_eqv_iff_packed :
    Eqv pe [X] (.cfg e (n + 1) blocks) (.cfg e' (m + 1) blocks') L ↔
      Eqv pe [X] (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).val
        (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).val [packedExitType L] := by
  refine (ofRegion_packExits_eq_iff (Step pe) (.cfg R he hb) (.cfg S he' hb')).symm.trans
    ((ofRegion_eq_iff (Step pe) _ _).trans ?_)
  exact ⟨fun h => (packExits_eqv_packed pe R he hb).symm.trans (h.trans (packExits_eqv_packed pe S he' hb')),
    fun h => (packExits_eqv_packed pe R he hb).trans (h.trans (packExits_eqv_packed pe S he' hb').symm)⟩

include pe in
theorem table_valid_iff_packed :
    Valid (ValueBranches.cfg R he hb).hasType (ValueBranches.cfg S he' hb').hasType ↔
      Valid (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property.hasType
        (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).property.hasType := by
  refine (valid_packExits_iff (.cfg R he hb) (.cfg S he' hb')).symm.trans ?_
  have left : Valid (ValueBranches.cfg R he hb).packExits.hasType
      (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property.hasType :=
    valid_of_eqv pe (packExits_eqv_packed pe R he hb) _ _
  have right : Valid (ValueBranches.cfg S he' hb').packExits.hasType
      (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).property.hasType :=
    valid_of_eqv pe (packExits_eqv_packed pe S he' hb') _ _
  exact ⟨fun h => Valid.trans (Valid.symm left) (Valid.trans h right),
    fun h => Valid.trans left (Valid.trans h (Valid.symm right))⟩

theorem table_reflects_iff_packed :
    Reflects pe (ValueBranches.cfg R he hb) (ValueBranches.cfg S he' hb') ↔
      Reflects pe (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property
        (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).property := by
  unfold Reflects
  exact imp_congr (table_valid_iff_packed pe R S he hb he' hb') (table_eqv_iff_packed pe R S he hb he' hb')

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
