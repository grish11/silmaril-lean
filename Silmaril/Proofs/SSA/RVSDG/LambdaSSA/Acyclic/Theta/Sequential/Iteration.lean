module

public import Silmaril.Semantics.Elgot.Thms

/-! # Two Elgot phases with only a forward handoff -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs

open Silmaril.Elgot

universe u
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable {I J M E : Type u}

private def dispatch (enter : M → E ⊕ J) : M → E ⊕ (I ⊕ J) :=
  fun mid => Sum.map id Sum.inr (enter mid)

private def grouped (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → E ⊕ J) :
    (I ⊕ J) → m ((E ⊕ (I ⊕ J)) ⊕ (I ⊕ J))
  | .inl i => first i >>= fun result => pure (Sum.map (dispatch enter) Sum.inl result)
  | .inr j => second j >>= fun result => pure (Sum.map Sum.inl Sum.inr result)

private theorem left_iter (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → E ⊕ J)
    (i : I) : iter (grouped first second enter) (.inl i) =
      iter first i >>= fun mid => pure (dispatch enter mid) := by
  let ret : M → E ⊕ (I ⊕ J) := dispatch enter
  have commute : (mapReturn first (pure ∘ ret) >=> liftPure (Sum.map id Sum.inl)) =
      (liftPure Sum.inl >=> grouped first second enter) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, mapReturn, pure_bind, bind_assoc, grouped]
    congr 1
    funext result
    cases result <;> simp [ret]
  have natural := congrFun (LawfulElgotMonad.naturality first (pure ∘ ret)) i
  have uniform := congrFun (LawfulElgotMonad.uniformity _ _ _ commute) i
  rw [← natural] at uniform
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] at uniform
  exact uniform.symm

private theorem right_iter (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → E ⊕ J)
    (j : J) : iter (grouped first second enter) (.inr j) =
      iter second j >>= fun out => pure (.inl out) := by
  let ret : E → E ⊕ (I ⊕ J) := Sum.inl
  have commute : (mapReturn second (pure ∘ ret) >=> liftPure (Sum.map id Sum.inr)) =
      (liftPure Sum.inr >=> grouped first second enter) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, mapReturn, pure_bind, bind_assoc, grouped]
    congr 1
    funext result
    cases result <;> simp [ret]
  have natural := congrFun (LawfulElgotMonad.naturality second (pure ∘ ret)) j
  have uniform := congrFun (LawfulElgotMonad.uniformity _ _ _ commute) j
  rw [← natural] at uniform
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] at uniform
  exact uniform.symm

theorem iter_sequential_select (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J))
    (enter : M → E ⊕ J) (flat : I ⊕ J → m (E ⊕ (I ⊕ J)))
    (left : ∀ i, flat (.inl i) = first i >>= fun r =>
      pure (Sum.elim (fun mid => Sum.map id Sum.inr (enter mid)) (Sum.inr ∘ Sum.inl) r))
    (right : ∀ j, flat (.inr j) = second j >>= fun r => pure (Sum.map id Sum.inr r))
    (i : I) : iter flat (.inl i) = iter first i >>= fun mid => Sum.elim pure (iter second) (enter mid) := by
  have flatten : flat = flattenBody (grouped first second enter) := by
    funext p
    cases p with
    | inl i =>
      rw [left]
      simp only [flattenBody, Bind.kleisliRight, liftPure, grouped, bind_assoc]
      congr 1
      funext r
      cases r with
      | inl mid => cases enter mid <;> simp [Silmaril.Elgot.flatten, dispatch, *]
      | inr _ => simp [Silmaril.Elgot.flatten]
    | inr j =>
      rw [right]
      simp only [flattenBody, Bind.kleisliRight, liftPure, grouped, bind_assoc]
      congr 1
      funext r
      cases r <;> simp [Silmaril.Elgot.flatten]
  rw [flatten, ← LawfulElgotMonad.codiagonal]
  rw [congrFun (LawfulElgotMonad.fixpoint (iter (grouped first second enter))) (.inl i),
    left_iter, bind_assoc]
  congr 1
  funext mid
  rw [pure_bind]
  cases selected : enter mid with
  | inl label => simp [dispatch, selected]
  | inr j =>
    simp only [dispatch, selected, Sum.map_inr, Sum.elim_inr]
    rw [congrFun (LawfulElgotMonad.fixpoint (iter (grouped first second enter))) (.inr j),
      right_iter, bind_assoc]
    simp

theorem iter_sequential (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → J)
    (flat : I ⊕ J → m (E ⊕ (I ⊕ J)))
    (left : ∀ i, flat (.inl i) = first i >>= fun r =>
      pure (.inr (Sum.elim (Sum.inr ∘ enter) Sum.inl r)))
    (right : ∀ j, flat (.inr j) = second j >>= fun r => pure (Sum.map id Sum.inr r))
    (i : I) : iter flat (.inl i) = iter first i >>= fun mid => iter second (enter mid) := by
  apply iter_sequential_select first second (Sum.inr ∘ enter) flat _ right i
  intro j
  rw [left]
  congr 1
  funext r
  cases r <;> rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs
