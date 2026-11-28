module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs

/-! # The retained-state fold for a common guarded round -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumCofan sumIso)
open Paper.WithCaseReturns.BinaryFold (alternatingStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {D B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "Tagged" => Silmaril.coprod D D

/-- Forget the outer tag and retain the payload on either arm. -/
noncomputable def fold (D : τ) : Obj (Silmaril.coprod D D) ⟶ Obj D :=
  (sumIso D D).hom ≫ coprod.desc (𝟙 (Obj D)) (𝟙 (Obj D))

/-- The guarded case representative of the payload-preserving fold. -/
def foldRegion : Region Φ :=
  .case (.var 0) (.br 0 (.var 0)) (.br 0 (.var 0))

theorem foldRegion_guarded (D : τ) : ValueBranches [Silmaril.coprod D D] (foldRegion (Φ := Φ)) [D] :=
  .case (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 0) rfl (.var rfl))

/-- Update the retained payload by one guarded round and forward it. -/
noncomputable def single {work : Region Φ} (hw : ValueBranches [D] work [D]) : Obj D ⟶ Obj B ⨿ Obj D :=
  ofRegion hw ≫ coprod.inr

/-- Forward the updated payload into the opposite outer tag on each arm. -/
noncomputable def switched {work : Region Φ} (hw : ValueBranches [D] work [D]) : Obj Tagged ⟶ Obj B ⨿ Obj Tagged :=
  split (B := B) (fold D) (ofRegion hw) (sumCofan D D).inr (sumCofan D D).inl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained
