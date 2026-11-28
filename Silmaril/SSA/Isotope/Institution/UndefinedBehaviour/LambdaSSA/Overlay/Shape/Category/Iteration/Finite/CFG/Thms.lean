module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Comparison
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Router

/-! # Complete observations and refinement of typed positional overlay CFGs -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG

open Syntax

universe u x

variable {σ : Type x}
variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X A B : Syntax.Ty}
variable {n states captures seeds results : Nat}

/-- A typed constructor jump has one ordinary return at the same state. -/
theorem observe_jump {Γ L : List Syntax.Ty} (prim : StatePrimitives Φ σ) (env : Bindings Γ)
    (i : Fin L.length) (typed : L.get i = A) (a : Expr Γ A) (s : σ) :
    Shape.denote (jump (Φ := Φ) i typed a) (model prim env) s =
      WithTop.some {Outcome.ret i (a.eval env).val s} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.observe_jump prim env i typed a s

/-- The actual positional overlay CFG has the observation computed by the
bounded traversal of its syntax-generated rows. -/
theorem classify_region (cfg : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin n) (input : Expr [X] A) (s : Fin states) :
    let env := emptyBindings.push (codes.capture c)
    Shape.denote (cfg.region i input) (model prim env) s =
      (execute (cfg.generate codes prim c) (encode codes i (input.eval env) s)).behaviour
        ((packedCodes n codes).carrier prim) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.classify_region
    cfg codes prim c i input s

/-- Iterating the exact-sum dispatcher agrees with the typed positional CFG.
The equality includes fresh top, returned payload and state, fault state,
primitive divergence and infinite replay. -/
theorem region_eq_exactSum (cfg : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin n) (input : Expr [X] A) (s : Fin states) :
    let env := emptyBindings.push (codes.capture c)
    Shape.denote (cfg.region i input) (model prim env) s =
      (iterateSum (cfg.step prim (codes.capture c))).run 0 (pack i (input.eval env)) s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.region_eq_exactSum
    cfg codes prim c i input s

/-- At each coded capture, the Boolean check decides refinement across all
common entry labels, constructor inputs and initial states. -/
theorem check_region_iff (lower upper : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) :
    check (lower.generate codes prim) (upper.generate codes prim) = true ↔
      ∀ (c : Fin captures) (i : Fin n) (input : Expr [X] A) (s : Fin states),
        let M := model prim (emptyBindings.push (codes.capture c))
        Shape.denote (lower.region i input) M s ≤ Shape.denote (upper.region i input) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.check_region_iff
    lower upper codes prim

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
