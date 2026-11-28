module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exit Exits exit_type resultBehaviour)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (observe_packedRequest_bind unpack_pack)
open Syntax (Bindings Expr Payload emptyBindings model)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

theorem inContext_eval {Γ : List Syntax.Ty} {A : Syntax.Ty} (a : Expr [] A) (env : Bindings Γ) :
    (inContext a).eval env = a.eval emptyBindings := by
  induction a with
  | var i => exact i.elim0
  | unit => rfl
  | pair a b left right => simp [inContext, Expr.eval, left, right]
  | inl a ih => simp [inContext, Expr.eval, ih]
  | inr a ih => simp [inContext, Expr.eval, ih]

private def constructorTerm {F : Type u} : Value Unit → Option (LambdaSSA.Tm F)
  | .atom _ => none
  | .unit => some .unit
  | .pair a b => LambdaSSA.Tm.pair <$> constructorTerm a <*> constructorTerm b
  | .inl a => LambdaSSA.Tm.inl <$> constructorTerm a
  | .inr a => LambdaSSA.Tm.inr <$> constructorTerm a

private theorem quote_operand {F : Type u} {Γ : List Syntax.Ty} {A : Syntax.Ty}
    (a : Expr [] A) : constructorTerm (F := F) (operandValue a) =
      some ((inContext (Γ := Γ) a).term (Φ := F)) := by
  induction a with
  | var i => exact i.elim0
  | unit => rfl
  | pair a b left right =>
    change (LambdaSSA.Tm.pair <$> constructorTerm (operandValue a) <*> constructorTerm (operandValue b)) = _
    rw [left, right]
    rfl
  | inl a ih =>
    change (LambdaSSA.Tm.inl <$> constructorTerm (operandValue a)) = _
    rw [ih]
    rfl
  | inr a ih =>
    change (LambdaSSA.Tm.inr <$> constructorTerm (operandValue a)) = _
    rw [ih]
    rfl

theorem operand_term_eq {F : Type u} {Γ : List Syntax.Ty} {A : Syntax.Ty}
    {a b : Expr [] A} (same : operandValue a = operandValue b) :
    ((inContext (Γ := Γ) a).term (Φ := F)) = (inContext (Γ := Γ) b).term := by
  have h := congrArg (constructorTerm (F := F)) same
  rw [quote_operand (Γ := Γ), quote_operand (Γ := Γ)] at h
  exact Option.some.inj h

private theorem packedRequest_congr {Γ : List Syntax.Ty} {f : Φ}
    {arg arg' : Expr [] (instrSrc f)} (same : operandValue arg = operandValue arg') :
    (CFG.Dependent.packedRequest f (inContext (Γ := Γ) arg) (S.target f)) =
      CFG.Dependent.packedRequest f (inContext arg') (S.target f) := by
  have native : Syntax.Program.requestRegion f (inContext (Γ := Γ) arg) =
      Syntax.Program.requestRegion f (inContext arg') :=
    Subtype.ext (congrArg (fun a => LambdaSSA.Region.br 0 (.op f a)) (operand_term_eq same))
  unfold CFG.Dependent.packedRequest CFG.Dependent.packedRequestTo
  rw [native]

private theorem inhabited_payload {α : Type v} {atomType : α → Empty → Prop}
    {a : Value α} {A : Syntax.Ty} (h : Shape.ValueTyped atomType a A) : Nonempty (Payload A) := by
  induction h with
  | @atom a A _ => exact A.elim
  | unit => exact ⟨⟨.unit, .unit⟩⟩
  | pair _ _ left right =>
    obtain ⟨a⟩ := left
    obtain ⟨b⟩ := right
    exact ⟨⟨.pair a.val b.val, .pair a.property b.property⟩⟩
  | inl _ left =>
    obtain ⟨a⟩ := left
    exact ⟨⟨.inl a.val, .inl a.property⟩⟩
  | inr _ right =>
    obtain ⟨a⟩ := right
    exact ⟨⟨.inr a.val, .inr a.property⟩⟩

theorem shaped_sound (p q : Tree S.replies) (h : p.Refines q) {Γ : List Syntax.Ty}
    (M : Shape.Model.{u,0,v,w} Φ Γ) (s : M.raw.σ) :
    Shape.denote (p.region S) M s ≤ Shape.denote (q.region S) M s := by
  induction p generalizing q Γ with
  | stop a =>
    cases q with
    | stop b =>
      rcases h with top | same
      · subst b
        exact le_top
      · subst b
        exact le_rfl
    | ask => exact False.elim h
  | ask f arg arms ih =>
    cases q with
    | stop b =>
      cases b with
      | ub => exact le_top
      | ret => exact False.elim h
    | ask g arg' next =>
      obtain ⟨rfl, same, compares⟩ := h
      change Shape.denote (.lsubst
          (CFG.Dependent.packedRequest f (inContext arg) (S.target f)) (fun i => (arms i).region S)) M s ≤
        Shape.denote (.lsubst
          (CFG.Dependent.packedRequest f (inContext arg') (S.target f)) (fun i => (next i).region S)) M s
      rw [packedRequest_congr (S := S) same]
      refine Shape.lsubst_mono_typed _ _ _ M s ?_
      intro i a typed t
      exact ih i (next i) (compares i (inhabited_payload typed)) (M.extend typed) t

theorem finite_observe {Γ : List Syntax.Ty} {n : Nat} (p : Tree S.replies)
    (h : Handler S.replies n) (env : Bindings Γ) (s : Fin n) :
    Shape.denote (p.region S) (model (S.primitives h) env) s = resultBehaviour (p.execute h s) := by
  induction p generalizing Γ s with
  | stop e =>
    cases e with
    | ub => rfl
    | ret i =>
      exact CFG.observe_jump (L := Exits) (S.primitives h) env i (exit_type i) .unit s
  | ask f arg arms ih =>
    rw [Tree.region, observe_packedRequest_bind, Tree.execute, inContext_eval]
    unfold RequestSignature.primitives operandValue
    cases h f (arg.eval emptyBindings).val s with
    | fault | diverge => rfl
    | reply i a t =>
      let enter (p : CFG.Dependent.Packet (S.replies f)) :=
        Shape.denote ((arms p.1).region S) (model (S.primitives h) (env.push p.2)) t
      let packet := CFG.Dependent.pack (L := S.replies f) ⟨i, a⟩
      let typeEq := congrArg Payload (S.target f)
      change enter (CFG.Dependent.unpack (cast typeEq (cast typeEq.symm packet))) = _
      have roundtrip : cast typeEq (cast typeEq.symm packet) = packet := by simp [cast_cast]
      rw [roundtrip, unpack_pack]
      exact ih i (env.push a) t

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
