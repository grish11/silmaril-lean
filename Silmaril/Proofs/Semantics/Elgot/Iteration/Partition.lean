module

public import Silmaril.Semantics.Elgot.Partition.Defs

public section

namespace Silmaril.Proofs.Semantics.Elgot

open Silmaril.Elgot

universe u v

theorem flatten_partition {m : Type u → Type v} [Monad m] [LawfulMonad m] {A B : Type u}
    (body : A → m (B ⊕ A)) (inner : A → Bool) :
    flattenBody (partitionStep body inner) = body := by
  funext state
  have flattenInner (next : B ⊕ A) : flatten (Sum.map Sum.inl id next) = next := by
    cases next <;> rfl
  by_cases h : inner state = true
  · simp only [flattenBody, Bind.kleisliRight, liftPure, Function.comp_apply, partitionStep, ite_eq_left h, bind_map_left]
    calc
      _ = body state >>= pure := bind_congr fun next => congrArg pure (flattenInner next)
      _ = _ := bind_pure _
  · simp only [flattenBody, Bind.kleisliRight, liftPure, Function.comp_apply, partitionStep, ite_eq_right h,
      bind_map_left, flatten, Sum.elim_inl, id_eq, bind_pure]

theorem flatten_partition_target {m : Type u → Type v} [Monad m] [LawfulMonad m] {A B : Type u}
    (body : A → m (B ⊕ A)) (inner : A → Bool) :
    flattenBody (partitionStepByTarget body inner) = body := by
  funext state
  have flat (transfer : B ⊕ A) : flatten (partitionTransfer inner transfer) = transfer := by
    cases transfer with
    | inl result => rfl
    | inr next => by_cases h : inner next = true <;> simp [partitionTransfer, flatten, h]
  simp only [flattenBody, Bind.kleisliRight, liftPure, Function.comp_apply, partitionStepByTarget, bind_map_left, flat]
  exact bind_pure _

end Silmaril.Proofs.Semantics.Elgot
