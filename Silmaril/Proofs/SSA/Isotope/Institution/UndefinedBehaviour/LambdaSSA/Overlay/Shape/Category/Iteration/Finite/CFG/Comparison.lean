module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Router
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (row_behaviour)

universe u

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {X A B : Silmaril.Ty Empty}
variable {n states captures seeds results : Nat}

private theorem carrier_encode (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (i : Fin n) (a : Payload A) (s : Fin states) :
    ((packedCodes n codes).carrier prim).invocation (encode codes i a s) = (pack i a, s) := by
  let seed := (packedCodes n codes).seed
  change (let p := finProdFinEquiv.symm (finProdFinEquiv (seed.symm (pack i a), s))
          (seed p.1, p.2)) = _
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

private theorem invocation_encode (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (i : Fin n) (a : Payload A) (s : Fin states) :
    invocation codes prim (encode codes i a s) = (label i, a.val, s) := by
  unfold invocation
  rw [carrier_encode]
  simp only [unpack_pack]

private theorem encode_decode (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (p : Fin ((n * seeds) * states)) :
    let input := ((packedCodes n codes).carrier prim).invocation p
    let decoded := unpack input.1
    encode codes decoded.1 decoded.2 input.2 = p := by
  dsimp only
  rw [encode, pack_unpack]
  let seed := (packedCodes n codes).seed
  change finProdFinEquiv (seed.symm (seed (finProdFinEquiv.symm p).1), (finProdFinEquiv.symm p).2) = p
  rw [Equiv.symm_apply_apply]
  exact finProdFinEquiv.apply_symm_apply p

private theorem row_positional (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (answer : Answer (.coprod B (Packet A n)) states) :
    (answer.row (packedCodes n codes)).positional ((packedCodes n codes).carrier prim)
      (invocation codes prim) = positionalAnswer answer := by
  cases answer with
  | ub | fault | diverge => rfl
  | ret p t =>
    obtain ⟨_, typed⟩ := p
    cases typed with
    | inl typed =>
      let b : Payload B := ⟨_, typed⟩
      change WithTop.some (Set.singleton (Feedback.external (labels A n) [B]
        (Outcome.ret 0 (codes.result (codes.result.symm b)).val t))) = _
      rw [Equiv.apply_symm_apply]
      rfl
    | inr typed =>
      let packet : Payload (Packet A n) := ⟨_, typed⟩
      let decoded := unpack packet
      have eq : finProdFinEquiv ((packedCodes n codes).seed.symm packet, t) =
          encode codes decoded.1 decoded.2 t := by
        unfold encode
        rw [pack_unpack]
      change (Row.repeat _).positional ((packedCodes n codes).carrier prim)
        (invocation codes prim) = _
      rw [eq, Row.positional, Row.routed]
      simp only [Carrier.positional, invocation_encode]
      rfl

private theorem classify_exactSum (cfg : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (p : Fin ((n * seeds) * states)) :
    let C := (packedCodes n codes).carrier prim
    (iterateSum (cfg.step prim (codes.capture c))).run 0 (C.invocation p).1 (C.invocation p).2 =
      (execute (cfg.generate codes prim c) p).behaviour C := by
  let C := (packedCodes n codes).carrier prim
  apply classify_sum C
  intro q
  let input := C.invocation q
  let decoded := unpack input.1
  let env := (emptyBindings.push (codes.capture c)).push decoded.2
  exact (observe_eval prim (cfg.block decoded.1) env input.2).trans
    (row_behaviour (packedCodes n codes) prim ((cfg.block decoded.1).eval prim env input.2)).symm

theorem classify_region (cfg : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin n) (input : Expr [X] A) (s : Fin states) :
    let env := emptyBindings.push (codes.capture c)
    Shape.denote (cfg.region i input) (model prim env) s =
      (execute (cfg.generate codes prim c) (encode codes i (input.eval env) s)).behaviour
        ((packedCodes n codes).carrier prim) := by
  let env := emptyBindings.push (codes.capture c)
  let a := input.eval env
  let p := encode codes i a s
  let C := (packedCodes n codes).carrier prim
  let entry := jump (Φ := Φ) (Feedback.internal (labels A n) [B] (label i)) (internal_type i) input
  let run := feedbackRun entry cfg.routed (model prim env).raw
  change Feedback.close run (.entry s) = (execute (cfg.generate codes prim c) p).behaviour C
  have enters : run (.entry s) = WithTop.some {Outcome.ret (Feedback.internal (labels A n) [B] (label i)) a.val s} :=
    observe_jump prim env _ (internal_type i) input s
  calc
    _ = Feedback.close run (.block (label i) a.val s) := close_branch (f := run) enters
    _ = Feedback.close run (invocationPoint (invocation codes prim) p) := by
      rw [invocationPoint, invocation_encode]
    _ = _ := by
      apply classify_positional C _ _ p
      intro q
      let arg := C.invocation q
      let target := unpack arg.1
      change denote (cfg.routed (label target.1)) (extendModel (model prim env).raw target.2.val) arg.2 = _
      exact (observe_routed cfg prim (label target.1) env target.2 arg.2).trans
        (row_positional codes prim ((cfg.block target.1).eval prim (env.push target.2) arg.2)).symm

theorem region_eq_exactSum (cfg : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) (c : Fin captures) (i : Fin n) (input : Expr [X] A) (s : Fin states) :
    let env := emptyBindings.push (codes.capture c)
    Shape.denote (cfg.region i input) (model prim env) s =
      (iterateSum (cfg.step prim (codes.capture c))).run 0 (pack i (input.eval env)) s := by
  let env := emptyBindings.push (codes.capture c)
  have closed := classify_exactSum cfg codes prim c (encode codes i (input.eval env) s)
  dsimp only at closed
  rw [carrier_encode] at closed
  exact (classify_region cfg codes prim c i input s).trans closed.symm

theorem expr_exists {Γ : List (Silmaril.Ty Empty)} (env : Bindings Γ) (a : Payload A) :
    ∃ e : Expr Γ A, e.eval env = a := by
  obtain ⟨_, typed⟩ := a
  induction typed with
  | atom h => exact h.elim
  | unit => exact ⟨.unit, rfl⟩
  | pair _ _ e f =>
    obtain ⟨e, he⟩ := e
    obtain ⟨f, hf⟩ := f
    exact ⟨.pair e f, by rw [Expr.eval, he, hf]; rfl⟩
  | inl _ e =>
    obtain ⟨e, he⟩ := e
    exact ⟨.inl e, Subtype.ext (congrArg (Isotope.Value.inl ∘ Subtype.val) he)⟩
  | inr _ e =>
    obtain ⟨e, he⟩ := e
    exact ⟨.inr e, Subtype.ext (congrArg (Isotope.Value.inr ∘ Subtype.val) he)⟩

theorem check_region_iff (lower upper : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) :
    check (lower.generate codes prim) (upper.generate codes prim) = true ↔
      ∀ (c : Fin captures) (i : Fin n) (input : Expr [X] A) (s : Fin states),
        let M := model prim (emptyBindings.push (codes.capture c))
        Shape.denote (lower.region i input) M s ≤ Shape.denote (upper.region i input) M s := by
  rw [check_behaviour_iff ((packedCodes n codes).carrier prim)]
  constructor
  · intro checked c i input s
    dsimp only
    rw [classify_region lower codes, classify_region upper codes]
    exact checked c (encode codes i (input.eval (emptyBindings.push (codes.capture c))) s)
  · intro compared c p
    let C := (packedCodes n codes).carrier prim
    let env := emptyBindings.push (codes.capture c)
    let arg := C.invocation p
    let target := unpack arg.1
    obtain ⟨e, computed⟩ := expr_exists env target.2
    have le := compared c target.1 e arg.2
    dsimp only at le
    rw [classify_region lower codes, classify_region upper codes, computed] at le
    have same : encode codes target.1 target.2 arg.2 = p := encode_decode codes prim p
    rwa [same] at le

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
