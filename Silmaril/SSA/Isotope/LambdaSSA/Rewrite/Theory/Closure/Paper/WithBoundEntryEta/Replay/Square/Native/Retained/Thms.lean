module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame

/-! # Exact retained-state fold and single/doubled endpoints -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumCofan sumIso)
open Paper.WithCaseReturns.BinaryFold (alternatingStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {D B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "Tagged" => Silmaril.coprod D D

/-- The left injection followed by the fold retains its payload. -/
theorem foldInl : (sumCofan (Φ := Φ) D D).inl ≫ fold D = 𝟙 (Obj D) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.foldInl

/-- The right injection followed by the fold retains its payload. -/
theorem foldInr : (sumCofan (Φ := Φ) D D).inr ≫ fold D = 𝟙 (Obj D) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.foldInr

/-- The categorical fold is represented by the guarded case on the input tag. -/
theorem fold_eq_case (D : τ) : fold (Φ := Φ) D = ofRegion (foldRegion_guarded (Φ := Φ) D) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.fold_eq_case D

/-- The two-arm retained frame gives the actual BinaryFold step. -/
theorem switched_eq {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    switched (B := B) hw = alternatingStep (single (B := B) hw) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.switched_eq hw

/-- The step square is native even for the payload-retaining fold. -/
theorem fold_square {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    alternatingStep (single (B := B) hw) ≫ coprod.map (𝟙 (Obj B)) (fold D) =
      fold D ≫ single (B := B) hw :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.fold_square hw

/-- Before iteration, the fold of the one-round source determines the
target step exactly. -/
theorem fold_square_iff_single {work : Region Φ} (hw : ValueBranches [D] work [D])
    (target : Obj D ⟶ Obj B ⨿ Obj D) :
    alternatingStep (single (B := B) hw) ≫ coprod.map (𝟙 (Obj B)) (fold D) =
      fold D ≫ target ↔ single (B := B) hw = target :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.fold_square_iff_single hw target

/-- One round followed by the identity constructor yields the exact single step. -/
theorem single_eq {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    ofRegion (repeating_guarded (B := B) hw (.var (i := 0) rfl)) ≫ (sumIso B D).hom =
      single (B := B) hw :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.single_eq hw

/-- Two guarded rounds with the same repeat constructor yield the exact doubled step. -/
theorem doubled_eq {work : Region Φ} (hw : ValueBranches [D] work [D]) :
    let g := single (B := B) hw
    ofRegion (repeating_guarded (B := B) (CfgEta.TypeCategory.seqValueBranches hw hw)
      (.var (i := 0) rfl)) ≫ (sumIso B D).hom = g ≫ coprod.desc coprod.inl g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.RetainedNativeFrame.doubled_eq hw

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained
