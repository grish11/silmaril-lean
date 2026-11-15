module

public import Silmaril.Wasm.Abstract.Loop.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.Abstract.Body.Thms

/-!
# Abstract Wasm loops: proofs

Each loop body runs to an immediate return, an immediate trap, or one import
call followed by a return; `toAFun_iter` and the iteration shapes of
`AFun.iter` then give the denotations.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Loop

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.Loop Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

theorem run_continue (a : A) (s : S) :
    (((pure (.inr a) : BodyM E S T (B ⊕ A))).run s).run = ret (.ok (.inr a, s)) := rfl

theorem run_trap {X : Type (u + 1)} (t : T) (s : S) :
    ((trap t : BodyM E S T X).run s).run = ret (.error t) := by
  simp [trap, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.run,
    ExceptT.mk, Functor.map, ExceptT.map, StateT.run]
  rfl

theorem run_poll (m : E.Op) (a : A) (s : S) :
    (((callImport m >>= fun _ => pure (.inr a)) : BodyM E S T (B ⊕ A)).run s).run =
      vis (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩ fun _ => ret (.ok (.inr a, s)) := by
  rw [StateT.run_bind, ExceptT.run_bind]
  refine (vis_bind (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩ _ _).trans ?_
  congr 1
  funext r
  exact pure_bind _ _

theorem toAFun_spin (s : S) (a : A) : toAFun (spin : Hom E S T A B) s a = {([], .div)} := by
  rw [spin, loop, toAFun_iter]
  exact AFun.iter_continue (fun s a => toAFun_of_run_ret (run_continue a s)) s a

theorem toAFun_trapLoop (t : T) (s : S) (a : A) :
    toAFun (trapLoop t : Hom E S T A B) s a = {([], .trap)} := by
  rw [trapLoop, loop, toAFun_iter]
  exact AFun.iter_trap (fun s a => toAFun_of_run_ret (run_trap t s)) s a

theorem toAFun_pollLoop (m : E.Op) (s : S) (a : A) :
    toAFun (pollLoop m : Hom E S T A B) s a = ∅ := by
  rw [pollLoop, loop, toAFun_iter]
  refine AFun.iter_productive (fun s a x hx => ?_) s a
  obtain ⟨cs, r, hp, rfl⟩ := hx
  rw [run_poll] at hp
  obtain ⟨n, cs', rfl, hp'⟩ := path_vis_inv hp
  obtain ⟨rfl, rfl⟩ := path_ret_iff.1 hp'
  exact ⟨by simp, a, s, rfl⟩

theorem collapse_iter_diverge {X : Type (u + 1)} (G : X → Tree (SigEv E) (B ⊕ X))
    (hG : ∀ x, G x = diverge) (x : X) : Silmaril.Elgot.iter G x = diverge := by
  rw [congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint G) x, hG, diverge_bind]

theorem collapse_trapLoop (t : T) (a : A) :
    collapse (trapLoop t a : BodyM E S T B) = collapse (spin a : BodyM E S T B) := by
  rw [trapLoop, spin, loop, loop, collapse_iter, collapse_iter]
  funext s
  change Silmaril.Elgot.iter _ (a, s) = Silmaril.Elgot.iter _ (a, s)
  rw [collapse_iter_diverge _ (fun p => by
    simp only [Silmaril.Elgot.StateT.body, collapse_trap]; exact diverge_bind _)]
  have : (Silmaril.Elgot.StateT.body fun a => collapse (pure (Sum.inr a) : BodyM E S T (B ⊕ A))) =
      fun p => (pure (.inr p) : Tree (SigEv E) ((B × S) ⊕ (A × S))) := by
    funext p
    simp only [Silmaril.Elgot.StateT.body, collapse_pure, StateT.run_pure, pure_bind,
      Function.comp]
    rfl
  rw [this, iterate_forever]

/-- Two bodies that trap with different payloads. -/
noncomputable def trapWith (b : Bool) : Hom Sig.empty.{0} PUnit.{2} (ULift.{1} Bool) PUnit.{2} PUnit.{2} :=
  fun _ => trap ⟨b⟩

theorem toAFun_not_injective : trapWith true ≠ trapWith false ∧
    toAFun (trapWith true) = toAFun (trapWith false) := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrArg (fun f => ((f ⟨⟩).run ⟨⟩).run) h
    simp only [trapWith, run_trap, ret_inj, Except.error.injEq, ULift.up.injEq] at this
    exact Bool.noConfusion this
  · funext s a
    rw [toAFun_of_run_ret (f := trapWith true) (run_trap _ s),
      toAFun_of_run_ret (f := trapWith false) (run_trap _ s)]
    rfl

end Silmaril.Proofs.Wasm.Abstract.Loop
