module

public import Silmaril.Semantics.IterOps.Defs

/-!
# Premonoidal Elgot structure: proofs

Kleisli families of lawful Elgot monads are lawful, and the laws transfer
backwards along faithful operation-preserving maps.
-/

public section

namespace Silmaril.Proofs.Semantics.IterOps

open Silmaril.IterOps

universe u w

theorem kleisli_lawful (m : Type u → Type u) [Monad m] [LawfulMonad m] [Silmaril.Elgot.Iterate m]
    [Silmaril.Elgot.LawfulElgotMonad m] : (kleisliOps m).Lawful where
  id_comp f := by funext a; simp [kleisliOps]
  comp_id f := by funext a; simp [kleisliOps]
  comp_assoc f g h := by funext a; simp [kleisliOps]
  pure_id A := rfl
  pure_comp f g := by funext a; simp [kleisliOps]
  inl_case f g := by funext a; simp [kleisliOps]
  inr_case f g := by funext a; simp [kleisliOps]
  case_comp f g h := by funext x; cases x <;> simp [kleisliOps]
  fixpoint f := Silmaril.Elgot.LawfulElgotMonad.fixpoint f
  naturality f g := Silmaril.Elgot.LawfulElgotMonad.naturality f g
  codiagonal f := Silmaril.Elgot.LawfulElgotMonad.codiagonal f
  uniformity f g h comm := Silmaril.Elgot.LawfulElgotMonad.uniformity f g h comm
  whisker_id C A := by funext p; simp [kleisliOps]
  whisker_comp C f g := by funext p; simp [kleisliOps]
  whisker_pure C f := by funext p; simp [kleisliOps, Prod.map]
  pure_central h f := by funext p; simp [kleisliOps]

variable {H H' : Type u → Type u → Type w} {o : Ops H} {o' : Ops H'}

theorem transfer (F : Hom o o') (h : o'.Lawful) : o.Lawful where
  id_comp f := F.faithful (by rw [F.map_comp, F.map_id, h.id_comp])
  comp_id f := F.faithful (by rw [F.map_comp, F.map_id, h.comp_id])
  comp_assoc f g k := F.faithful (by simp only [F.map_comp, h.comp_assoc])
  pure_id A := F.faithful (by rw [F.map_pure, F.map_id, h.pure_id])
  pure_comp f g := F.faithful (by rw [F.map_comp, F.map_pure, F.map_pure, F.map_pure, h.pure_comp])
  inl_case f g := F.faithful (by rw [F.map_comp, F.map_pure, F.map_case, h.inl_case])
  inr_case f g := F.faithful (by rw [F.map_comp, F.map_pure, F.map_case, h.inr_case])
  case_comp f g k := F.faithful (by
    rw [F.map_comp, F.map_case, F.map_case, F.map_comp, F.map_comp, h.case_comp])
  fixpoint f := F.faithful (by
    rw [F.map_iter, F.map_comp, F.map_case, F.map_id, F.map_iter]; exact h.fixpoint _)
  naturality f g := F.faithful (by
    rw [F.map_comp, F.map_iter, F.map_iter, F.map_comp, F.map_case, F.map_comp, F.map_pure,
      F.map_pure, h.naturality])
  codiagonal f := F.faithful (by
    rw [F.map_iter, F.map_iter, F.map_iter, F.map_comp, F.map_pure, h.codiagonal])
  uniformity f g k comm := by
    have comm' : o'.comp (F.map f) (o'.pure (Sum.map _root_.id k)) =
        o'.comp (o'.pure k) (F.map g) := by
      have := congrArg F.map comm
      rwa [F.map_comp, F.map_comp, F.map_pure, F.map_pure] at this
    exact F.faithful (by rw [F.map_iter, F.map_comp, F.map_pure, F.map_iter,
      h.uniformity _ _ k comm'])
  whisker_id C A := F.faithful (by rw [F.map_whisker, F.map_id, F.map_id, h.whisker_id])
  whisker_comp C f g := F.faithful (by
    rw [F.map_whisker, F.map_comp, F.map_comp, F.map_whisker, F.map_whisker, h.whisker_comp])
  whisker_pure C f := F.faithful (by rw [F.map_whisker, F.map_pure, F.map_pure, h.whisker_pure])
  pure_central k f := F.faithful (by
    simp only [F.map_comp, F.map_whisker, F.map_pure]; exact h.pure_central _ _)

end Silmaril.Proofs.Semantics.IterOps
