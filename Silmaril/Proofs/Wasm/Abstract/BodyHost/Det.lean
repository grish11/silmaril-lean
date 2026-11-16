module

public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.HostRun.Defs
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic

/-!
# Bodies are deterministic given the answers, finished and pending runs together (proofs)

Two runs of one interaction tree agree until the answers differ. That holds
for two finished paths (`path_agree`), and also for a finished path against a
pending call and for two pending calls. So `DetP (toAFun f) (toPending f)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree
open Silmaril.Proofs.Wasm.Abstract.BodyTrace (vis_heq path_agree)

universe u

variable {S B : Type (u + 1)}

theorem pagree_of_agree {E : Sig.{u}} {S B : Type u} :
    ∀ {c₁ c₂ : List (Call E)} {e₁ e₂ : End S B}, AFun.Agree c₁ e₁ c₂ e₂ →
      PAgree c₁ (.inl e₁) c₂ (.inl e₂)
  | [], [], _, _, h => h
  | ⟨_, _⟩ :: _, ⟨_, _⟩ :: _, _, _, h => ⟨h.1, fun hn => pagree_of_agree (h.2 hn)⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

theorem answer_eq {E : Sig.{u}} {R : Type u} {e : SigEv E R} {n n' : R}
    (hn : HEq (ULift.up.{u + 1} (cast e.2.symm n)) (ULift.up.{u + 1} (cast e.2.symm n'))) : n = n' := by
  have hn' : cast e.2.symm n = cast e.2.symm n' := congrArg ULift.down (eq_of_heq hn)
  simpa using congrArg (cast e.2) hn'

theorem pend_path {E : Sig.{u}} {A : Type (u + 1)} {t : Tree (SigEv E) A} {cs : List (Call E)}
    {m : E.Op} (h : Pend t cs m) :
    ∀ {cs' : List (Call E)} {r : PathEnd A} {e : End S B}, Path t cs' r →
      PAgree (cs.map liftCall) (.inr (ULift.up m)) (cs'.map liftCall) (.inl e) := by
  induction h with
  | here ht =>
    intro cs' r e hp
    cases hp with
    | ret ht' => rw [ht] at ht'; exact absurd ht'.symm (ret_ne_vis _ _ _)
    | div ht' => rw [ht] at ht'; exact absurd ht' (vis_ne_diverge _ _)
    | vis ht' _ =>
      rw [ht] at ht'
      obtain ⟨rfl, he, -⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      rfl
  | @vis t R ev k n cs m ht _ ih =>
    intro cs' r e hp
    cases hp with
    | ret ht' => rw [ht] at ht'; exact absurd ht'.symm (ret_ne_vis _ _ _)
    | div ht' => rw [ht] at ht'; exact absurd ht' (vis_ne_diverge _ _)
    | vis ht' hp' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, hk⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      refine ⟨rfl, fun hn => ?_⟩
      obtain rfl := answer_eq hn
      exact ih hp'

theorem path_pend {E : Sig.{u}} {A : Type (u + 1)} {t : Tree (SigEv E) A} {cs : List (Call E)}
    {m : E.Op} (h : Pend t cs m) :
    ∀ {cs' : List (Call E)} {r : PathEnd A} {e : End S B}, Path t cs' r →
      PAgree (cs'.map liftCall) (.inl e) (cs.map liftCall) (.inr (ULift.up m)) := by
  induction h with
  | here ht =>
    intro cs' r e hp
    cases hp with
    | ret ht' => rw [ht] at ht'; exact absurd ht'.symm (ret_ne_vis _ _ _)
    | div ht' => rw [ht] at ht'; exact absurd ht' (vis_ne_diverge _ _)
    | vis ht' _ =>
      rw [ht] at ht'
      obtain ⟨rfl, he, -⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      rfl
  | @vis t R ev k n cs m ht _ ih =>
    intro cs' r e hp
    cases hp with
    | ret ht' => rw [ht] at ht'; exact absurd ht'.symm (ret_ne_vis _ _ _)
    | div ht' => rw [ht] at ht'; exact absurd ht' (vis_ne_diverge _ _)
    | vis ht' hp' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, hk⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      refine ⟨rfl, fun hn => ?_⟩
      obtain rfl := answer_eq hn
      exact ih hp'

theorem pend_pend {E : Sig.{u}} {A : Type (u + 1)} {t : Tree (SigEv E) A} {cs : List (Call E)}
    {m : E.Op} (h : Pend t cs m) :
    ∀ {cs' : List (Call E)} {m' : E.Op}, Pend t cs' m' →
      PAgree (S := S) (B := B) (cs.map liftCall) (.inr (ULift.up m)) (cs'.map liftCall)
        (.inr (ULift.up m')) := by
  induction h with
  | here ht =>
    intro cs' m' hp
    cases hp with
    | here ht' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, -⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      rfl
    | vis ht' _ =>
      rw [ht] at ht'
      obtain ⟨rfl, he, -⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      rfl
  | @vis t R ev k n cs m ht _ ih =>
    intro cs' m' hp
    cases hp with
    | here ht' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, -⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      rfl
    | vis ht' hp' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, hk⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      refine ⟨rfl, fun hn => ?_⟩
      obtain rfl := answer_eq hn
      exact ih hp'

/-- **A body is deterministic given the answers**, finished and pending runs
together. -/
theorem detP {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    DetP (toAFun f) (toPending f) := by
  rintro s a x y (⟨cs, e, rfl, ⟨cs₀, r, hp, he⟩⟩ | ⟨cs, m, rfl, ⟨cs₀, m₀, hp, he⟩⟩) <;>
    rintro (⟨cs', e', rfl, ⟨cs₁, r', hp', he'⟩⟩ | ⟨cs', m', rfl, ⟨cs₁, m₁, hp', he'⟩⟩) <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
  · exact pagree_of_agree (path_agree hp hp')
  · exact path_pend hp' hp
  · exact pend_path hp hp'
  · exact pend_pend hp hp'

end Silmaril.Proofs.Wasm.Abstract.BodyHost
