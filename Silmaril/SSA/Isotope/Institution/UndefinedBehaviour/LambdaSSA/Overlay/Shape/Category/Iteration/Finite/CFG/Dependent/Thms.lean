module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Comparison
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Routing

/-! # Complete shaped observations of heterogeneous positional CFGs -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Syntax (Expr StatePrimitives Primitives emptyBindings Bindings.push model)

universe u x

variable {σ : Type x}
variable {Φ : Type u} [HasTy Φ Syntax.Ty] {X : Syntax.Ty}
variable {R L : List Syntax.Ty} {states captures seeds results : Nat}

/-- The selected packet keeps its payload and state at the destination
chosen by the ordered reply tag. -/
theorem observe_packedRequestTo {Γ : List Syntax.Ty} (prim : StatePrimitives Φ σ)
    (env : Syntax.Bindings Γ) (f : Φ) (arg : Expr Γ (instrSrc f))
    (typed : instrTrg f = LambdaSSA.Region.packedExitType R)
    (target : Fin R.length → Fin L.length) (routed : ∀ i, L.get (target i) = R.get i)
    (s : σ) :
    Shape.denote (packedRequestTo f arg typed target routed) (model prim env) s =
      match prim f (arg.eval env) s with
      | .ret a t =>
        let p := unpack (cast (congrArg Syntax.Payload typed) a)
        WithTop.some {Outcome.ret (target p.1) p.2.val t}
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.observe_packedRequestTo
    prim env f arg typed target routed s

/-- Dispatch an exact primitive reply and run only its selected continuation
at the reply state. The empty packet type has no successful reply. -/
theorem observe_packedRequest_bind {Γ : List Syntax.Ty} (prim : Primitives Φ states)
    (env : Syntax.Bindings Γ) (f : Φ) (arg : Expr Γ (instrSrc f))
    (typed : instrTrg f = LambdaSSA.Region.packedExitType R)
    (k : (i : Fin R.length) → Region Φ (R.get i :: Γ) L) (s : Fin states) :
    Shape.denote (.lsubst (packedRequest f arg typed) k) (model prim env) s =
      match prim f (arg.eval env) s with
      | .ret a t =>
        let p := unpack (cast (congrArg Syntax.Payload typed) a)
        Shape.denote (k p.1) (model prim (env.push p.2)) t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.observe_packedRequest_bind
    prim env f arg typed k s

/-- Every generated row equals the full observation of the original typed
routed block at that packet and machine state. -/
theorem generated_row (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (p : Fin (seeds * states)) :
    let env := emptyBindings.push (C.capture c)
    let input := C.invocation p
    Shape.denote (g.routed input.1.1) ((model prim env).extend input.1.2.property) input.2 =
      (g.generate C prim c p).routed C.carrier :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.generated_row
    g C prim c p

/-- The executable scan classifies the actual positional overlay feedback,
keeping the ordered exit position and the exact payload of an ordinary return. -/
theorem classify_region (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin R.length)
    (input : Expr [X] (R.get i)) (s : Fin states) :
    let env := emptyBindings.push (C.capture c)
    Shape.denote (g.region i input) (model prim env) s =
      (execute (g.generate C prim c) (C.invocation.symm (⟨i, input.eval env⟩, s))).routed C.carrier :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.classify_region
    g C prim c i input s

/-- Packing only the external return tags identifies the positional CFG
observation with the existing exact-sum iterator on its typed dispatcher. -/
theorem region_eq_exactSum (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin R.length)
    (input : Expr [X] (R.get i)) (s : Fin states) :
    let env := emptyBindings.push (C.capture c)
    packBehaviour (L := L) (Shape.denote (g.region i input) (model prim env) s) =
      (iterateSum (g.step prim (C.capture c))).run 0 (pack ⟨i, input.eval env⟩) s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.region_eq_exactSum
    g C prim c i input s

/-- Compare the existing shaped order for each coded capture, every common
entry label with its exact operand type, and every initial machine state. -/
theorem check_region_iff (lower upper : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) :
    check (lower.generate C prim) (upper.generate C prim) = true ↔
      ∀ (c : Fin captures) (i : Fin R.length) (input : Expr [X] (R.get i)) (s : Fin states),
        let M := model prim (emptyBindings.push (C.capture c))
        Shape.denote (lower.region i input) M s ≤ Shape.denote (upper.region i input) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.check_region_iff
    lower upper C prim

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
