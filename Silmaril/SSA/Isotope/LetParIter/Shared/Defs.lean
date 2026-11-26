module

public import Silmaril.SSA.Isotope.LetPar.Interpretation.Defs
public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs

/-! # Instantiate the shared tier interpreter with native LetIter models -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [Elgot.Iterate m] [InstructionModel Φ τ ε m]

@[instance_reducible] def nativeProductModel : Isotope.Semantics.ProductModel (TyDen (τ := τ)) :=
  ⟨TypeModel.productEquiv⟩

@[instance_reducible] def nativeUnitModel : Isotope.Semantics.UnitModel (TyDen (τ := τ)) :=
  ⟨TypeModel.unitEquiv.trans
    ⟨fun _ => PUnit.unit, fun _ => (), fun _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _⟩⟩

/-- The iteration tier uses native sum and empty interpretations and Elgot feedback. -/
def nativeControl : Control .iter (TyDen (τ := τ)) m where
  sum _ := TypeModel.coprodEquiv
  zero _ := TypeModel.emptyEquiv.trans
    ⟨Empty.elim, PEmpty.elim, (fun e => nomatch e), (fun e => nomatch e)⟩
  loop _ := Elgot.iter

/-- Interpret an iterative program with the common evaluator and the native
type, instruction and environment interfaces used by the soundness theorem. -/
def interpret (P : Elgot.ParallelPairing m) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β a A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    m (TyDen A) :=
  letI := nativeProductModel (τ := τ)
  letI := nativeUnitModel (τ := τ)
  d.denote (TyDen (τ := τ)) ⟨denoteInstr (ε := ε)⟩ (fun x y => P.pair x y) nativeControl
    (fun x _ h => CtxDen.lookup γ x h) (BoundDen.get ρ)

end Silmaril.Isotope.LetParIter
