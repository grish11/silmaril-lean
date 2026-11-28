module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicReplyReadback

/-! # Standard Paper readback of typed acyclic control -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Extension.Singleton (iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {Φ : Type} [Profile Φ]

local notation "U" => nativeUnit Φ
local notation "X" => unitObj Φ
local notation "I" => iterateChosen (Seed Φ)
local notation "drop" => Paper.TypeCategory.discardArrow (Φ := Φ) (Silmaril.coprod UnitTy UnitTy)

/-- The emitted region has exactly the selected input and output shapes. -/
theorem Control.region_typed {s t : ReplyShape} (p : Control Φ s t) :
    ValueBranches [s.ty] p.region [t.ty] :=
  AcyclicReplyReadback.region_typed p

/-- The written region represents the original acyclic control arrow in standard Paper. -/
theorem Control.native_eq_ofRegion {s t : ReplyShape} (p : Control Φ s t) :
    p.native = Paper.TypeCategory.ofRegion p.region_typed :=
  AcyclicReplyReadback.native_region p

/-- A constructor path followed by dispatch selects exactly its native arm. -/
theorem point_dispatch {Y : Native Φ} (s : ReplyShape) (k : s.Value → (U ⟶ Y)) (x : s.Value) :
    point s x ≫ dispatch s k = k x :=
  AcyclicReplyReadback.point_dispatch s k x

/-- The typed written region is equal in standard Paper to the dispatch
of its read-back finite reply trees. -/
theorem Control.ofRegion_eq_readback {s t : ReplyShape} (p : Control Φ s t) :
    Paper.TypeCategory.ofRegion p.region_typed = dispatch s (fun x => (p.readback x).render (point t)) :=
  p.native_eq_ofRegion.symm.trans (AcyclicReplyReadback.control_readback p)

/-- A complete row reads back to one finite reply tree at its Unit input. -/
theorem Program.native_eq_render {α : Type} {Y : Native Φ} (p : Program Φ α)
    (leaf : α → (U ⟶ Y)) : p.native leaf = p.readback.render leaf :=
  AcyclicReplyReadback.program_readback p leaf

/-- An actual square on the original projected control arrows recovers
both standard Paper discard equations on the original native rows. -/
theorem square_iff_native_rows (left right : Program Φ Route) (target : Program Φ Bool) :
    sourceStep left right ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep target ↔
      left.native nativeRoute ≫ coprod.map (𝟙 U) drop = target.native nativeTarget ∧
      right.native nativeRoute ≫ coprod.map (𝟙 U) drop = target.native nativeTarget :=
  AcyclicReplyReadback.square_iff_native left right target

/-- Uniformity starts with the square on the original control arrows. The
reply-tree representatives are computed by readback. -/
theorem uniformity (left right : Program Φ Route) (target : Program Φ Bool)
    (square : sourceStep left right ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep target) :
    I (sourceStep left right) = fold ≫ I (targetStep target) :=
  AcyclicReplyReadback.uniformity left right target square

namespace Example

/-- The source has an additional constructor-controlled case before its
effectful sequel. The actual original-arrow square still commutes. -/
theorem square :
    sourceStep left right ≫ coprod.map (𝟙 (unitObj Op)) fold = fold ≫ targetStep target := by
  rw [AcyclicReplyReadback.source_readback, AcyclicReplyReadback.target_readback]
  exact (FiniteReplies.square_iff_codes _ _ _).2 AcyclicReplyReadback.example_codes

theorem iteration :
    iterateChosen (Seed Op) (sourceStep left right) = fold ≫ iterateChosen (Seed Op) (targetStep target) :=
  uniformity left right target square

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic
