module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Comparison
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Router
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Routing
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Answer Expr Payload Primitives emptyBindings Bindings.push model observe_eval)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.LambdaSSA.Region (packedExitType packedExitValue)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG (observe_jump expr_exists)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (row_behaviour)

universe u

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {X : Silmaril.Ty Empty}
variable {R L : List (Silmaril.Ty Empty)} {states captures seeds results : Nat}

private theorem row_routed (C : Codes X R L captures seeds results)
    (answer : Answer (.coprod (packedExitType L) (packedExitType R)) states) :
    (answer.row C.packed).routed C.carrier = routedAnswer answer := by
  cases answer with
  | ub | fault | diverge => rfl
  | ret p t =>
    obtain ⟨_, typed⟩ := p
    cases typed with
    | inl typed =>
      let b : Packed L := ⟨_, typed⟩
      let decode := fun out : Packet L => Feedback.external R L (Outcome.ret out.1 out.2.val t)
      change WithTop.some {decode (C.result (C.result.symm (unpack b)))} =
        WithTop.some {decode (unpack b)}
      rw [Equiv.apply_symm_apply]
    | inr typed =>
      let a : Packed R := ⟨_, typed⟩
      let p : Fin (seeds * states) := C.invocation.symm (unpack a, t)
      have decoded : C.invocation p = (unpack a, t) := C.invocation.apply_symm_apply _
      let observe (input : Packet R × Fin states) : Behaviour (R ++ L).length Unit (Fin states) :=
        WithTop.some {Outcome.ret (Feedback.internal R L input.1.1) input.1.2.val input.2}
      exact congrArg observe decoded

theorem generated_row (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (p : Fin (seeds * states)) :
    let env := emptyBindings.push (C.capture c)
    let input := C.invocation p
    Shape.denote (g.routed input.1.1) ((model prim env).extend input.1.2.property) input.2 =
      (g.generate C prim c p).routed C.carrier := by
  let env := emptyBindings.push (C.capture c)
  let input := C.invocation p
  exact (observe_routed g prim input.1.1 env input.1.2 input.2).trans
    (row_routed C ((g.block input.1.1).eval prim (env.push input.1.2) input.2)).symm

theorem classify_region (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin R.length)
    (input : Expr [X] (R.get i)) (s : Fin states) :
    let env := emptyBindings.push (C.capture c)
    Shape.denote (g.region i input) (model prim env) s =
      (execute (g.generate C prim c) (C.invocation.symm (⟨i, input.eval env⟩, s))).routed C.carrier := by
  let env := emptyBindings.push (C.capture c)
  let a := input.eval env
  let p : Fin (seeds * states) := C.invocation.symm (⟨i, a⟩, s)
  let entry := CFG.jump (Φ := Φ) (Feedback.internal R L i) (internal_type i) input
  let run := feedbackRun entry g.routed (model prim env).raw
  change Feedback.close run (.entry s) = (execute (g.generate C prim c) p).routed C.carrier
  have enters : run (.entry s) = WithTop.some {Outcome.ret (Feedback.internal R L i) a.val s} :=
    observe_jump prim env _ (internal_type i) input s
  calc
    _ = Feedback.close run (.block i a.val s) := close_branch (f := run) enters
    _ = Feedback.close run (invocationPoint C.carrier.invocation p) := by
      have decoded : C.invocation p = (⟨i, a⟩, s) := C.invocation.apply_symm_apply _
      let observe (input : Packet R × Fin states) : Behaviour L.length Unit (Fin states) :=
        Feedback.close run (.block input.1.1 input.1.2.val input.2)
      exact (congrArg observe decoded).symm
    _ = _ := classify_routed C.carrier (g.generate C prim c) p (generated_row g C prim c)

theorem check_region_iff (lower upper : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) :
    check (lower.generate C prim) (upper.generate C prim) = true ↔
      ∀ (c : Fin captures) (i : Fin R.length) (input : Expr [X] (R.get i)) (s : Fin states),
        let M := model prim (emptyBindings.push (C.capture c))
        Shape.denote (lower.region i input) M s ≤ Shape.denote (upper.region i input) M s := by
  rw [check_routed_iff C.carrier]
  constructor
  · intro checked c i input s
    dsimp only
    rw [classify_region lower C, classify_region upper C]
    exact checked c (C.invocation.symm (⟨i, input.eval (emptyBindings.push (C.capture c))⟩, s))
  · intro compared c p
    let arg := C.invocation p
    let env := emptyBindings.push (C.capture c)
    obtain ⟨e, computed⟩ := expr_exists env arg.1.2
    have le := compared c arg.1.1 e arg.2
    dsimp only at le
    rw [classify_region lower C, classify_region upper C, computed] at le
    have same : C.invocation.symm (⟨arg.1.1, arg.1.2⟩, arg.2) = p := C.invocation.symm_apply_apply p
    rwa [same] at le

theorem classify_exactSum (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (p : Fin (seeds * states)) :
    let input := C.invocation p
    (iterateSum (g.step prim (C.capture c))).run 0 (pack input.1) input.2 =
      (execute (g.generate C prim c) p).behaviour (C.packed.carrier prim) := by
  change (iterateSum (g.step prim (C.capture c))).run 0 ((C.packed.carrier prim).invocation p).1
    ((C.packed.carrier prim).invocation p).2 = _
  apply classify_sum (C.packed.carrier prim)
  intro q
  let arg := C.invocation q
  let env := (emptyBindings.push (C.capture c)).push arg.1.2
  change Shape.denote (g.block (unpack (pack arg.1)).1).region
    (model prim ((emptyBindings.push (C.capture c)).push (unpack (pack arg.1)).2)) arg.2 = _
  rw [unpack_pack]
  exact (observe_eval prim (g.block arg.1.1) env arg.2).trans
    (row_behaviour C.packed prim ((g.block arg.1.1).eval prim env arg.2)).symm

private theorem pack_result (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (r : Result results states) :
    packBehaviour (L := L) (r.routed C.carrier) = r.behaviour (C.packed.carrier prim) := by
  cases r with
  | ub => rfl
  | fault | diverge => simp [Result.routed, Result.behaviour, packBehaviour, packOutcome, Codes.carrier, Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.Codes.carrier]
  | ret b t =>
    change WithTop.some (Set.image (packOutcome (L := L))
      {Outcome.ret (C.result b).1 (C.result b).2.val t}) =
      returnPayload (pack (C.result b)).val t
    rw [Set.image_singleton, pack_value]
    rfl

theorem region_eq_exactSum (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin R.length)
    (input : Expr [X] (R.get i)) (s : Fin states) :
    let env := emptyBindings.push (C.capture c)
    packBehaviour (L := L) (Shape.denote (g.region i input) (model prim env) s) =
      (iterateSum (g.step prim (C.capture c))).run 0 (pack ⟨i, input.eval env⟩) s := by
  let env := emptyBindings.push (C.capture c)
  let a := input.eval env
  let p : Fin (seeds * states) := C.invocation.symm (⟨i, a⟩, s)
  have decoded : C.invocation p = (⟨i, a⟩, s) := C.invocation.apply_symm_apply _
  have closed := classify_exactSum g C prim c p
  dsimp only at closed
  rw [decoded] at closed
  dsimp only
  erw [classify_region g C prim c i input s, pack_result C prim]
  exact closed.symm

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
