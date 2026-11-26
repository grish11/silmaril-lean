module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Structured.Defs
public import Silmaril.Semantics.ITree.Reindex.Thms

public section

namespace Silmaril.Proofs.LetIter.Reindex.Structured

open Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.Reindex Silmaril.Isotope.LetIter.Reindex.Structured
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured (Event Lifted toSmall)

universe u

variable {α : Type u} {V W : α → Type u}

theorem request_inverse {Φ : Type u} [HasTy Φ (Ty α)]
    (e : ∀ a, V a ≃ W a) (q : ITree.Request (Event (Φ := Φ) V)) :
    (signatureEquiv (fun a => (e a).symm)).request ((signatureEquiv e).request q) = q := by
  rcases q with ⟨_, ⟨f, x⟩⟩
  have hx := (typeEquiv e (instrSrc f)).symm_apply_apply x
  rw [typeEquiv_symm] at hx
  exact congrArg (fun y => (⟨_, Event.call (V := V) f y⟩ : ITree.Request (Event (Φ := Φ) V))) hx

theorem toSmall_natural (e : ∀ a, V a ≃ W a) (A : Ty α) (x : Ty.denote (Lifted V) A) :
    toSmall W A (typeEquiv (liftedEquiv e) A x) = typeEquiv e A (toSmall V A x) := by
  induction A with
  | base => rfl
  | unit => rfl
  | empty => exact PEmpty.elim x
  | product A B ihA ihB => exact Prod.ext (ihA x.1) (ihB x.2)
  | coprod A B ihA ihB =>
    cases x with
    | inl a => exact congrArg Sum.inl (ihA a)
    | inr b => exact congrArg Sum.inr (ihB b)

theorem call_natural {Φ : Type u} [HasTy Φ (Ty α)]
    (e : ∀ a, V a ≃ W a) (f : Φ) (x : Ty.denote (Lifted V) (instrSrc f)) :
    (signatureEquiv (Φ := Φ) e).tree (typeEquiv (liftedEquiv e) (instrTrg f))
      ((callInstructions V).eval f x) =
    (callInstructions W).eval f (typeEquiv (liftedEquiv e) (instrSrc f) x) := by
  simp only [callInstructions, ITree.SignatureEquiv.tree_vis, ITree.SignatureEquiv.tree_ret]
  let B : Ty α := instrTrg f
  let k (r : Ty.denote W B) :=
    typeEquiv (liftedEquiv e) B ((toSmall V B).symm ((typeEquiv e B).symm r))
  change ITree.vis (Event.call (V := W) f (typeEquiv e (instrSrc f) (toSmall V (instrSrc f) x)))
      (fun r => ITree.ret (k r)) =
    ITree.vis (Event.call (V := W) f (toSmall W (instrSrc f) (typeEquiv (liftedEquiv e) (instrSrc f) x)))
      (fun r => ITree.ret ((toSmall W B).symm r))
  rw [toSmall_natural]
  apply congrArg (ITree.vis (Event.call (V := W) f _))
  funext r
  apply congrArg ITree.ret
  apply (toSmall W B).injective
  simp [k, toSmall_natural]

end Silmaril.Proofs.LetIter.Reindex.Structured
