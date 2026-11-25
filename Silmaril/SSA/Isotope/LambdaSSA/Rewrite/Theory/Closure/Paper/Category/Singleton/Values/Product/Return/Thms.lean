module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductReturn

/-! # The sequential expression witness for singleton pairing -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Pairing two typed returns runs the left expression, then the right expression in the
original input context, then returns their constructor pair. -/
theorem pairArrows_returnTerm {X A B : τ} {a b : Tm Φ}
    (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B) :
    pairArrows (returnTerm ha) (returnTerm hb) =
      returnTerm (.let₁ ha (.let₁ (hb.rename (Ren.wk [X] A))
        (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductReturn.pairArrows_returnTerm ha hb

/-- Sequential pairing admits a pure term witness when both legs do. -/
theorem pureReturn_pairArrows {ε : Type w} [HasEff Φ ε] {pe : ε}
    {X A B : TypeCategory (τ := τ) Φ} {f : X ⟶ A} {g : X ⟶ B}
    (hf : PureReturn pe f) (hg : PureReturn pe g) :
    PureReturn pe (pairArrows (τ := τ) f g) := by
  obtain ⟨_, ha, pa, rfl⟩ := hf
  obtain ⟨_, hb, pb, rfl⟩ := hg
  exact ⟨_, _, .let₁ pa (.let₁ (pb.rename Nat.succ) (.pair .var .var)), pairArrows_returnTerm ha hb⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
