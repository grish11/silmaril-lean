module

public import Silmaril.Wasm.Abstract.Body.Defs

/-!
# Abstract Wasm function bodies: proofs

The library's lawful Elgot monads satisfy λiter's lawful-Elgot class (same
laws), and the trap-to-divergence collapse is a monad morphism.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Body

open Silmaril.Games Silmaril.Wasm.Abstract.Body

universe u

theorem thesisLawful (m : Type u → Type u) [Monad m] [LawfulMonad m] [Silmaril.Elgot.Iterate m]
    [Silmaril.Elgot.LawfulElgotMonad m] :
    @Silmaril.Thesis.Elgot.LawfulElgotMonad m _ _ (thesisIterate m) :=
  @Silmaril.Thesis.Elgot.LawfulElgotMonad.mk m _ _ (thesisIterate m)
    (fun f => Silmaril.Elgot.LawfulElgotMonad.fixpoint f)
    (fun f g => Silmaril.Elgot.LawfulElgotMonad.naturality f g)
    (fun f => Silmaril.Elgot.LawfulElgotMonad.codiagonal f)
    (fun f g h comm => Silmaril.Elgot.LawfulElgotMonad.uniformity f g h comm)

variable {E : Sig.{u}} {S T : Type (u + 1)}

theorem collapse_pure {A : Type (u + 1)} (a : A) :
    collapse (pure a : BodyM E S T A) = (pure a : BodyC E S A) := by
  funext s
  change ((pure a : BodyM E S T A).run s).run >>= _ = (pure a : BodyC E S A).run s
  rw [StateT.run_pure, ExceptT.run_pure, pure_bind, StateT.run_pure]

theorem collapse_bind {A B : Type (u + 1)} (x : BodyM E S T A) (f : A → BodyM E S T B) :
    collapse (x >>= f) = (collapse x >>= fun a => collapse (f a)) := by
  funext s
  change ((x >>= f).run s).run >>= _ = (collapse x >>= fun a => collapse (f a)).run s
  rw [StateT.run_bind, ExceptT.run_bind, StateT.run_bind, bind_assoc]
  change _ = ((x.run s).run >>= _) >>= _
  rw [bind_assoc]
  congr 1
  funext r
  cases r with
  | error e =>
    simp only [pure_bind]
    exact (Silmaril.Elgot.ITree.diverge_bind _).symm
  | ok p =>
    simp only [pure_bind]
    rfl

theorem collapse_trap {A : Type (u + 1)} (t : T) :
    collapse (trap t : BodyM E S T A) = fun _ => Silmaril.Elgot.ITree.diverge := by
  funext s
  simp [collapse, trap, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.run,
    ExceptT.mk, Functor.map, ExceptT.map]

theorem trap_bind {A B : Type (u + 1)} (t : T) (f : A → BodyM E S T B) :
    (trap t >>= f : BodyM E S T B) = trap t := by
  funext s
  change ((trap t >>= f : BodyM E S T B).run s) = (trap t : BodyM E S T B).run s
  rw [StateT.run_bind]
  simp only [trap, throw, throwThe, MonadExceptOf.throw]
  apply ExceptT.ext
  simp [ExceptT.run_bind, throwThe, MonadExceptOf.throw, ExceptT.run_mk]

theorem handle_raise {B X : Type (u + 1)} (h : X → BodyM E S T B) :
    handle (fun x : X => (raise x : BodyM E S T (B ⊕ X))) h = h := by
  funext x
  simp [handle, raise]

theorem handle_trap {A B X : Type (u + 1)} (t : T) (h : X → BodyM E S T B) :
    handle (fun _ : A => (trap t : BodyM E S T (B ⊕ X))) h = fun _ => trap t := by
  funext a
  exact trap_bind t _

theorem collapse_raise {B X : Type (u + 1)} (x : X) :
    collapse (raise x : BodyM E S T (B ⊕ X)) = (pure (.inr x) : BodyC E S (B ⊕ X)) :=
  collapse_pure _

end Silmaril.Proofs.Wasm.Abstract.Body
