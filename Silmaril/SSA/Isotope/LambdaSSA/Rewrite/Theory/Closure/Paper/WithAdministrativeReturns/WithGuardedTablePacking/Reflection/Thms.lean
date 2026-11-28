module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.ExitPacking.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Reduction

/-! # Table reflection reduces to packed single-feedback dispatchers

Soundness gives `Eqv → Valid`. Reflection is the converse. For nonempty
guarded tables with any ordered exits, both the contextual equation and
validity in every model are unchanged by passing to the packed readback
representatives. No reflection is proved in this file.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Every contextual equation of this quotient is valid in every model. -/
theorem valid_of_eqv {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Eqv pe Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) : Valid hr hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.valid_of_eqv pe e hr hs

/-- With soundness, reflection at two regions says that the contextual
equation and validity in every model coincide there. -/
theorem reflects_iff {X : τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches [X] r L) (hs : ValueBranches [X] s L) :
    Reflects pe hr hs ↔ (Valid hr.hasType hs.hasType ↔ Eqv pe [X] r s L) :=
  ⟨fun h => ⟨h, fun e => valid_of_eqv pe e _ _⟩, fun h => h.1⟩

/-- Tagging the exits neither adds nor removes equalities of models. -/
theorem valid_packExits_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Valid hr.packExits.hasType hs.packExits.hasType ↔ Valid hr.hasType hs.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.valid_packExits_iff hr hs

variable {n m : Nat} (R : Fin (n + 1) → τ) (S : Fin (m + 1) → τ) {X : τ} {L : LCtx τ}
  {e e' : Region Φ} {blocks : Fin (n + 1) → Region Φ} {blocks' : Fin (m + 1) → Region Φ}
  (he : ValueBranches [X] e (List.ofFn R ++ L))
  (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L))
  (he' : ValueBranches [X] e' (List.ofFn S ++ L))
  (hb' : ∀ i, ValueBranches [S i, X] (blocks' i) (List.ofFn S ++ L))

/-- Two written tables are equal at their written exits exactly when
their packed dispatcher representatives are equal at the packed exit.
The tables may differ in arity and in row types. -/
theorem table_eqv_iff_packed :
    Eqv pe [X] (.cfg e (n + 1) blocks) (.cfg e' (m + 1) blocks') L ↔
      Eqv pe [X] (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).val
        (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).val [packedExitType L] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.table_eqv_iff_packed pe R S he hb he' hb'

include pe in
/-- The same reduction for validity in every model. -/
theorem table_valid_iff_packed :
    Valid (ValueBranches.cfg R he hb).hasType (ValueBranches.cfg S he' hb').hasType ↔
      Valid (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property.hasType
        (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).property.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.table_valid_iff_packed pe R S he hb he' hb'

/-- Reflection at two written tables is reflection at their packed
single-feedback dispatchers. -/
theorem table_reflects_iff_packed :
    Reflects pe (ValueBranches.cfg R he hb) (ValueBranches.cfg S he' hb') ↔
      Reflects pe (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property
        (packedReadbackRep S (tagExits_entry S he') (tagExits_row S hb')).property :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.table_reflects_iff_packed pe R S he hb he' hb'

/-- Reflection on the packed fragment at the packed exit type gives
reflection for all nonempty guarded tables with exits `L`. -/
theorem table_reflects_of_packed (packed : PackedReflection (Φ := Φ) pe X (packedExitType L)) :
    Reflects pe (ValueBranches.cfg R he hb) (ValueBranches.cfg S he' hb') :=
  (table_reflects_iff_packed pe R S he hb he' hb').2
    (packed R S (tagExits_entry R he) (tagExits_row R hb) (tagExits_entry S he') (tagExits_row S hb'))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
