module

public import Silmaril.Games.Abstract.Exception.Defs

/-!
# Exception properties of abstract functions: proofs
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Exception

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.AFun

universe u

variable {E : Sig.{u}} {S A R R' X : Type u}

theorem noEscape_mono {f g : AFun E S A (R ⊕ X)} (h : f ≤ g) (hg : NoEscape g) : NoEscape f :=
  fun s a ⟨c, x, s', hx⟩ => hg s a ⟨c, x, s', h s a hx⟩

theorem seqX_noEscape {f : AFun E S A (R ⊕ X)} {g : AFun E S R (R' ⊕ X)} (hf : NoEscape f)
    (hg : NoEscape g) : NoEscape (seqX f g) := by
  rintro s a ⟨c, y, s', hx⟩
  rcases hx with ⟨c₀, -, he⟩ | ⟨c₀, -, he⟩ | ⟨c₁, b, s₁, c₂, e, h₁, h₂, he⟩
  · simp at he
  · simp at he
  · simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    rcases b with v | x₀
    · exact hg s₁ v ⟨c₂, y, s', h₂⟩
    · exact hf s a ⟨c₁, x₀, s₁, h₁⟩

theorem handleX_noEscape (f : AFun E S A (R ⊕ X)) {h : AFun E S X (R ⊕ X)} (hh : NoEscape h) :
    NoEscape (handleX f h) := by
  rintro s a ⟨c, y, s', hx⟩
  rcases hx with ⟨c₀, -, he⟩ | ⟨c₀, -, he⟩ | ⟨c₁, b, s₁, c₂, e, -, h₂, he⟩
  · simp at he
  · simp at he
  · simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    rcases b with v | x₀
    · simp only [catchWith, Set.mem_singleton_iff, Prod.mk.injEq] at h₂
      cases h₂.2
    · exact hh s₁ x₀ ⟨c₂, y, s', h₂⟩

theorem noEscapeUnder_of {f : AFun E S A (R ⊕ X)} (h : NoEscape f) (Q : Call E → Prop) :
    NoEscapeUnder Q f :=
  noEscape_mono (fun _ _ _ hx => hx.1) h

theorem noEscapeUnder_mono {Q Q' : Call E → Prop} (hQ : ∀ y, Q y → Q' y) {f : AFun E S A (R ⊕ X)}
    (h : NoEscapeUnder Q' f) : NoEscapeUnder Q f :=
  noEscape_mono (fun _ _ x hx => show x ∈ underAssm Q' f _ _ from
    ⟨hx.1, fun y hy => hQ y (hx.2 y hy)⟩) h

/-- Raise at once. -/
def raiseNow : AFun Sig.empty.{0} PUnit.{1} PUnit.{1} (PUnit.{1} ⊕ PUnit.{1}) := fun s _ => {([], .ret (.inr ⟨⟩) s)}

/-- Return at once. -/
def retNow : AFun Sig.empty.{0} PUnit.{1} PUnit.{1} (PUnit.{1} ⊕ PUnit.{1}) := fun s _ => {([], .ret (.inl ⟨⟩) s)}

theorem retNow_noEscape : NoEscape retNow := by
  rintro s a ⟨c, x, s', hx⟩
  simp [retNow] at hx

theorem seqX_raise_mayEscape : MayEscape (seqX raiseNow retNow) ⟨⟩ ⟨⟩ :=
  ⟨[], ⟨⟩, ⟨⟩, .inr (.inr ⟨[], .inr ⟨⟩, ⟨⟩, [], .ret (.inr ⟨⟩) ⟨⟩, rfl, rfl, rfl⟩)⟩

end Silmaril.Proofs.Games.Abstract.Exception
