module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame

/-! # Native composition at the specialized recurrent endpoint -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumCofan sumIso)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B D E I X Y L R : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "State" => Silmaril.coprod X Y

/-- Build the exact guarded round with a typed initializer, a typed discriminator, and guarded arms and table. -/
theorem letCaseTable_guarded {n : Nat} {init disc : Tm Φ} {left right : Region Φ}
    {rows : Fin n → Region Φ} (labels : Fin n → τ)
    (hi : Tm.HasType [D] init I) (hd : Tm.HasType [I, D] disc (Silmaril.coprod L R))
    (hl : ValueBranches [L, I, D] left (List.ofFn labels ++ [E]))
    (hr : ValueBranches [R, I, D] right (List.ofFn labels ++ [E]))
    (hb : ∀ j, ValueBranches [labels j, D] (rows j) (List.ofFn labels ++ [E])) :
    ValueBranches [D] (letCaseTable init disc left right rows) [E] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.letCaseTable_guarded labels hi hd hl hr hb

/-- A constructor repeat supplies the guarded exit after the round. -/
theorem repeating_guarded {work : Region Φ} {reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (hb : Tm.BranchValue [E] reply D) :
    ValueBranches [D] (repeating work reply) [Silmaril.coprod B D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.repeating_guarded hw hb

/-- Substitution of the structural state map preserves the guarded step. -/
theorem specialize_guarded {r : Region Φ} {state : Tm Φ}
    (ha : Tm.BranchValue [A] state D) (hr : ValueBranches [D] r [B]) :
    ValueBranches [A] (r.substVars (Tm.singleSubst state ∘ lift Nat.succ)) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.specialize_guarded ha hr

/-- The recurrent region represents the guarded round followed by the constructor repeat injection. -/
theorem repeating_composite {work : Region Φ} {reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (hb : Tm.BranchValue [E] reply D) :
    ofRegion (repeating_guarded (B := B) hw hb) ≫ (sumIso B D).hom =
      ofRegion hw ≫ ofRegion (.br (ℓ := 0) rfl hb) ≫ coprod.inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.repeating_composite hw hb

/-- The native source composite in a linear frame is the repeat endpoint of the specialized guarded round. -/
theorem linear_composite {work : Region Φ} {state reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (ha : Tm.BranchValue [A] state D)
    (hb : Tm.BranchValue [E] reply D) (next : Obj E ⟶ Obj A)
    (recurs : next ≫ ofRegion (.br (ℓ := 0) rfl ha) = ofRegion (.br (ℓ := 0) rfl hb)) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    linear (B := B) h (ofRegion hw) next ≫ coprod.map (𝟙 (Obj B)) h =
      ofRegion (specialize_guarded ha (repeating_guarded (B := B) hw hb)) ≫ (sumIso B D).hom :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.linear_composite hw ha hb next recurs

/-- Postcompose the recursive routes armwise before choosing a syntactic
representative for the state map. -/
theorem split_post (h : Obj State ⟶ Obj D) (work : Obj D ⟶ Obj E)
    (nextLeft nextRight : Obj E ⟶ Obj State) (reply : Obj E ⟶ Obj D)
    (leftRecurs : nextLeft ≫ h = reply) (rightRecurs : nextRight ≫ h = reply) :
    split (B := B) h work nextLeft nextRight ≫ coprod.map (𝟙 (Obj B)) h =
      h ≫ work ≫ reply ≫ coprod.inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.split_post
    h work nextLeft nextRight reply leftRecurs rightRecurs

/-- Each input arm may supply its own next state. The native composite uses the common specialized round when the two next-state arrows agree after the state map. -/
theorem split_composite {work : Region Φ} {state reply : Tm Φ}
    (hw : ValueBranches [D] work [E]) (ha : Tm.BranchValue [State] state D)
    (hb : Tm.BranchValue [E] reply D) (nextLeft nextRight : Obj E ⟶ Obj State)
    (leftRecurs : nextLeft ≫ ofRegion (.br (ℓ := 0) rfl ha) = ofRegion (.br (ℓ := 0) rfl hb))
    (rightRecurs : nextRight ≫ ofRegion (.br (ℓ := 0) rfl ha) = ofRegion (.br (ℓ := 0) rfl hb)) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    split (B := B) h (ofRegion hw) nextLeft nextRight ≫ coprod.map (𝟙 (Obj B)) h =
      ofRegion (specialize_guarded ha (repeating_guarded (B := B) hw hb)) ≫ (sumIso B D).hom :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NativeSquareFrame.split_composite hw ha hb nextLeft nextRight leftRecurs rightRecurs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame
