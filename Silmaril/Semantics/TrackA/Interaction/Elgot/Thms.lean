module

public import Silmaril.Semantics.TrackA.Interaction.Elgot.Defs
import Silmaril.Proofs.Semantics.TrackA.Interaction.Elgot.Laws

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction.Elgot

open Silmaril.Elgot

universe u v

variable {S : Signature.{u,u}} {X A C : Type u}

/-- A compatible infinite stream of replies is witnessed by a single infinite
exchange path in the checked delayed observation semantics. -/
theorem loop_observes_infinite (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (path : Nat → X)
    (reply : (n : Nat) → S.Response (request (path n)))
    (recurs : ∀ n, after (path n) (reply n) = .inr (path (n + 1))) :
    Trace.infinite (fun n => ⟨request (path n), reply n⟩) ∈
      (WeakITree.toDelayed (guardedLoop request after (path 0))).observes :=
  Proofs.Semantics.TrackA.Interaction.Elgot.loop_observes_infinite request after path reply recurs

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [∀ R : Type u, Small.{u} (WeakITree S R)]

/-- Interpreting a request-guarded loop is target iteration of the given
handler followed by the dependent continuation. -/
theorem interpret_guardedLoop (handler : Handler S m) (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (x : X) :
    (interpret handler).map (guardedLoop request after x) = iter (handledBody handler request after) x :=
  Proofs.Semantics.TrackA.Interaction.Elgot.interpret_guardedLoop handler request after x

/-- An effectful continuation on the returned value moves into the exit arm
of the interpreted iteration. Recursive states continue unchanged. -/
theorem interpret_guardedLoop_naturality (handler : Handler S m) (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (post : A → m C) (x : X) :
    ((interpret handler).map (guardedLoop request after x) >>= post) =
      iter (mapReturn (handledBody handler request after) post) x := by
  rw [interpret_guardedLoop]
  exact congrFun (LawfulElgotMonad.naturality (handledBody handler request after) post) x

/-- Two recursive exits can be merged into one when interpreting nested
iteration of the guarded body. -/
theorem interpret_nestedGuardedLoop (handler : Handler S m) (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → (A ⊕ X) ⊕ X) (x : X) :
    (interpret handler).map (iter (guardedLoop request after) x) =
      iter (flattenBody (handledBody handler request after)) x := by
  rw [(interpret handler).map_iter]
  simp only [interpret_guardedLoop]
  exact congrFun (LawfulElgotMonad.codiagonal (handledBody handler request after)) x

end Silmaril.Semantics.TrackA.Interaction.Elgot
