module

public import Silmaril.Semantics.TrackA.Interaction.Elgot.Defs

public section

namespace Silmaril.Proofs.Semantics.TrackA.Interaction.Elgot

open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Semantics.TrackA.Interaction.Elgot
open Silmaril.Elgot Silmaril.Elgot.ITree

universe u v

variable {S : Signature.{u,u}} {X A : Type u}

private theorem loop_unfold (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (x : X) :
    guardedLoop request after x = vis (.request (request x)) fun reply =>
      (after x reply).elim ret (guardedLoop request after) := by
  unfold guardedLoop
  rw [congrFun (iterate_fixpoint (guardedBody request after)) x]
  simp only [guardedBody, vis_bind]
  congr 1
  funext reply
  change pure (after x reply) >>= _ = _
  rw [pure_bind]
  rfl

theorem loop_observes_infinite (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (path : Nat → X)
    (reply : (n : Nat) → S.Response (request (path n)))
    (recurs : ∀ n, after (path n) (reply n) = .inr (path (n + 1))) :
    Trace.infinite (fun n => ⟨request (path n), reply n⟩) ∈
      (WeakITree.toDelayed (guardedLoop request after (path 0))).observes := by
  refine ⟨(), fun n => guardedLoop request after (path n), rfl, ?_⟩
  intro n
  refine ⟨guardedLoop request after (path n), .refl, ?_⟩
  have layer : WeakITree.unfold (guardedLoop request after (path n)) =
      .vis (request (path n)) (fun r => (after (path n) r).elim ret (guardedLoop request after)) := by
    rw [loop_unfold request after (path n), WeakITree.unfold_vis]
  simpa only [WeakITree.toDelayed, recurs n, Sum.elim_inr] using Coalgebra.Step.vis layer (reply n)

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [∀ R : Type u, Small.{u} (WeakITree S R)]

theorem interpret_guardedLoop (handler : Handler S m) (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (x : X) :
    (interpret handler).map (guardedLoop request after x) = iter (handledBody handler request after) x := by
  rw [guardedLoop, (interpret handler).map_iter]
  congr 1
  funext state
  change Interpret.fold (E := IndexedEvent S) (m := m) (indexedHandler handler) (guardedBody request after state) = _
  rw [guardedBody, Interpret.fold_vis]
  simp only [handledBody, indexedHandler, Interpret.fold_ret]

end Silmaril.Proofs.Semantics.TrackA.Interaction.Elgot
