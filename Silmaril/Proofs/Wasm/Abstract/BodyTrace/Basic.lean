module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Semantics.ITree.Thms

/-!
# From interaction-tree bodies to trace-set functions: proofs

Two finite paths of one interaction tree agree until their answers differ, so
denoted functions are deterministic given the history; a nondeterministic
function is not denoted.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree

universe u

theorem vis_heq {Ev : Type u → Type u} {A : Type (u + 1)} {R R' : Type u} {e : Ev R} {e' : Ev R'}
    {k : R → Tree Ev A} {k' : R' → Tree Ev A} (h : vis e k = vis e' k') :
    R = R' ∧ HEq e e' ∧ HEq k k' := by
  have := congrArg out h
  simp only [out_vis, Part.some_inj, Visible.vis.injEq] at this
  exact this

theorem path_agree {E : Sig.{u}} {S T B : Type (u + 1)}
    {t : Tree (SigEv E) (Except T (B × S))} {c₁ c₂ : List (Call E)}
    {r₁ r₂ : PathEnd (Except T (B × S))} (h₁ : Path t c₁ r₁) (h₂ : Path t c₂ r₂) :
    AFun.Agree (c₁.map liftCall) (endOf r₁) (c₂.map liftCall) (endOf r₂) := by
  induction h₁ generalizing c₂ r₂ with
  | ret ht =>
    cases h₂ with
    | ret ht' =>
      rw [ht] at ht'
      obtain rfl := ret_inj.1 ht'
      rfl
    | div ht' => rw [ht] at ht'; exact absurd ht' (ret_ne_diverge _)
    | vis ht' _ => rw [ht] at ht'; exact absurd ht' (ret_ne_vis _ _ _)
  | div ht =>
    cases h₂ with
    | ret ht' => rw [ht] at ht'; exact absurd ht'.symm (ret_ne_diverge _)
    | div _ => rfl
    | vis ht' _ => rw [ht] at ht'; exact absurd ht'.symm (vis_ne_diverge _ _)
  | @vis t R e k n cs r ht hp ih =>
    cases h₂ with
    | ret ht' => rw [ht] at ht'; exact absurd ht'.symm (ret_ne_vis _ _ _)
    | div ht' => rw [ht] at ht'; exact absurd ht' (vis_ne_diverge _ _)
    | @vis _ R' e' k' n' cs' r' ht' hp' =>
      rw [ht] at ht'
      obtain ⟨rfl, he, hk⟩ := vis_heq ht'
      obtain rfl := eq_of_heq he
      obtain rfl := eq_of_heq hk
      refine ⟨rfl, fun hn => ?_⟩
      have hn' : cast e.2.symm n = cast e.2.symm n' := by
        have := congrArg ULift.down (eq_of_heq hn)
        exact this
      have : n = n' := by
        have := congrArg (cast e.2) hn'
        simpa using this
      subst this
      exact ih hp'

theorem toAFun_det {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    AFun.Det (toAFun f) := by
  rintro s a x y ⟨cs, r, hp, rfl⟩ ⟨cs', r', hp', rfl⟩
  exact path_agree hp hp'

/-- A nondeterministic function: return `true` or `false`. -/
def coin : AFun (liftSig Sig.empty.{0}) PUnit.{2} PUnit.{2} (ULift.{1} Bool) := fun s _ =>
  {([], .ret ⟨true⟩ s), ([], .ret ⟨false⟩ s)}

theorem coin_not_det : ¬ AFun.Det coin := by
  intro h
  have := h ⟨⟩ ⟨⟩ ([], .ret ⟨true⟩ ⟨⟩) ([], .ret ⟨false⟩ ⟨⟩) (.inl rfl) (.inr rfl)
  simp [AFun.Agree] at this

theorem coin_not_denoted {T : Type 1} :
    ∀ f : Hom Sig.empty.{0} PUnit.{2} T PUnit.{2} (ULift.{1} Bool), toAFun f ≠ coin :=
  fun f h => coin_not_det (h ▸ toAFun_det f)

end Silmaril.Proofs.Wasm.Abstract.BodyTrace
