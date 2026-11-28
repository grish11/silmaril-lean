module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs

/-! # Returning terms with nested computed calls -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls

open Silmaril

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A typed return fragment closed under primitive calls, returning
sequences, and pure case analysis on the singleton input. -/
inductive ReturnFragment : {X D : τ} → {a : Tm Φ} → Tm.HasType [X] a D → Prop where
  | value {X D : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a D) : ReturnFragment ha.hasType
  | call {X : τ} {a : Tm Φ} (p : Φ) {ha : Tm.HasType [X] a (instrSrc p)} :
      ReturnFragment ha → ReturnFragment (.op (f := p) ha)
  | seq {X A D : τ} {a b : Tm Φ} {ha : Tm.HasType [X] a A} {hb : Tm.HasType [A] b D} :
      ReturnFragment ha → ReturnFragment hb →
      ReturnFragment (.let₁ ha (hb.rename ((Ren.wk [] X).lift A)))
  | caseInput {A B D : τ} {a b : Tm Φ} {ha : Tm.HasType [A] a D} {hb : Tm.HasType [B] b D}
      (pa : Tm.Pure pe a) (pb : Tm.Pure pe b) : ReturnFragment ha → ReturnFragment hb →
      ReturnFragment (.case (.var (i := 0) rfl)
        (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
