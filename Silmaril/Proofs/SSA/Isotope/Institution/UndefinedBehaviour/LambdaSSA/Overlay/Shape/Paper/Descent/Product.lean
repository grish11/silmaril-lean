module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Values
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops PureValue Realizes ShapedObs let₂_pure)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}

private theorem realize_pair {a b : Tm Φ} {l r : Value α}
    (left : PureValue O env a l) (right : PureValue O env b r) :
    Realizes O env (Tm.consSubst b (Tm.singleSubst a)) (extend (extend env l) r) := by
  intro i
  cases i with
  | zero => exact right
  | succ i => exact Realizes.single left i

theorem productBeta {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)} {r t : Region Φ}
    (h : Region.ProductBeta.Step Γ r t L) : ShapedObs (α := α) (σ := σ) Γ r t := by
  intro O _ _ env _
  cases h with
  | let₂Beta ha hb _ =>
    obtain ⟨_, left⟩ := PureValue.ofBranchValue (O := O) (env := env) ha
    obtain ⟨_, right⟩ := PureValue.ofBranchValue (O := O) (env := env) hb
    exact (let₂_pure (left.pair right) _).trans (((realize_pair left right).region _).symm)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
