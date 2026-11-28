module

public import Silmaril.Semantics.TrackA.Interaction.WeakITree.Thms
public import Silmaril.Semantics.ITreeInterpret.Thms

/-! # Iteration of interpreted dependent requests

The source is the existing weak ITree monad specialized to a dependent
signature. The target supplies a lawful monad and complete iteration (fixpoint,
effectful return naturality, codiagonal and uniformity for pure state maps).
The smallness hypothesis is on weak tree carriers over the chosen value
universe, including sum result types used in the iteration laws.
-/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction.Elgot

open Silmaril.Elgot Silmaril.Elgot.ITree

universe u v

variable {S : Signature.{u,u}} {m : Type u → Type v}

/-- Interpret each request as an effect returning its own dependent response. -/
abbrev Handler (S : Signature.{u,u}) (m : Type u → Type v) :=
  (q : S.Request) → m (S.Response q)

def indexedHandler (handler : Handler S m) : ITree.Handler (IndexedEvent S) m :=
  fun {_} event => match event with | .request q => handler q

/-- The existing fold gives all monad and iteration preservation fields for
this handler. Its existence needs smallness and the target Elgot laws. -/
noncomputable def interpret [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
    [∀ A : Type u, Small.{u} (WeakITree S A)] (handler : Handler S m) :
    Interpret.Hom (E := IndexedEvent S) (m := m) (indexedHandler handler) :=
  Interpret.foldHom (E := IndexedEvent S) (m := m) (indexedHandler handler)

variable {X A : Type u}

/-- Every return or recursive call in the body comes after one visible request. -/
def guardedBody (request : X → S.Request) (after : (x : X) → S.Response (request x) → A ⊕ X)
    (x : X) : WeakITree S (A ⊕ X) :=
  vis (.request (request x)) fun reply => ret (after x reply)

noncomputable def guardedLoop (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) : X → WeakITree S A :=
  iter (guardedBody request after)

/-- The Kleisli body of the interpreted loop. -/
def handledBody [Monad m] (handler : Handler S m) (request : X → S.Request)
    (after : (x : X) → S.Response (request x) → A ⊕ X) (x : X) : m (A ⊕ X) :=
  handler (request x) >>= fun reply => pure (after x reply)

end Silmaril.Semantics.TrackA.Interaction.Elgot
