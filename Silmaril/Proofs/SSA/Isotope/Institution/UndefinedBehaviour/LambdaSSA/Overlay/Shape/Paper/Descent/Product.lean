module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Values
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt PureValue Realizes ShapedObs)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}

theorem let₂_pure {a : Tm Φ} {l r : Value α} (pure : PureValue O env a (.pair l r))
    (p : Region Φ) : RegionAt O env (.let₂ a p) (extend (extend env l) r) p where
  eval := by
    intro s j a t
    constructor
    · intro run
      cases run with
      | let₂ arg body =>
        obtain ⟨eq, rfl⟩ := pure.unique arg
        cases eq
        exact body
    · exact fun run => .let₂ (pure.eval _) run
  fault := by
    intro s t
    constructor
    · intro run
      cases run with
      | let₂_arg arg => exact (pure.noFault arg).elim
      | let₂_body arg body =>
        obtain ⟨eq, rfl⟩ := pure.unique arg
        cases eq
        exact body
    · exact fun run => .let₂_body (pure.eval _) run
  div := by
    intro s
    constructor
    · intro run
      cases run.unfold with
      | let₂_arg arg => exact (pure.noDiv arg).elim
      | core step => cases step with
        | let₂ arg body =>
          obtain ⟨eq, rfl⟩ := pure.unique arg
          cases eq
          exact body
    · exact fun run => .fold_core (.let₂ (pure.eval _) run)

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
