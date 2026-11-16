module

public import Mathlib.Order.FixedPoints

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi

/-- One infinite path visits the accepting set arbitrarily late. No seriality,
finiteness or branching bound is assumed; a deadlock has no such path. -/
def Accepts {W : Type} (R : W → W → Prop) (F : Set W) (w : W) : Prop :=
  ∃ p : Nat → W, p 0 = w ∧ (∀ n, R (p n) (p (n+1))) ∧
    ∀ n, ∃ m, n ≤ m ∧ p m ∈ F

/-- A finite prefix of exactly n transitions, with a target at its last state. -/
def ReachIn {W : Type} (R : W → W → Prop) (T : Set W) : Nat → W → Prop
  | 0, w => w ∈ T
  | n+1, w => ∃ v, R w v ∧ ReachIn R T n v

/-- The inner μ operator: (F ∩ EX Z) ∪ EX Y. -/
def inner {W : Type} (R : W → W → Prop) (F Z : Set W) : Set W →o Set W where
  toFun Y := {w | (w ∈ F ∧ ∃ v, R w v ∧ v ∈ Z) ∨ ∃ v, R w v ∧ v ∈ Y}
  monotone' := by
    intro Y Y' h w hw
    rcases hw with hF | ⟨v, hr, hv⟩
    · exact Or.inl hF
    · exact Or.inr ⟨v, hr, h hv⟩

/-- The outer operator of ν Z. μ Y. ((F ∧ EX Z) ∨ EX Y). -/
noncomputable def outer {W : Type} (R : W → W → Prop) (F : Set W) : Set W →o Set W where
  toFun Z := (inner R F Z).lfp
  monotone' := by
    intro Z Z' h
    apply OrderHom.lfp.mono
    intro Y w hw
    rcases hw with ⟨hf, v, hr, hv⟩ | hY
    · exact Or.inl ⟨hf, v, hr, h hv⟩
    · exact Or.inr hY

end Silmaril.Logic.Temporal.Buchi
