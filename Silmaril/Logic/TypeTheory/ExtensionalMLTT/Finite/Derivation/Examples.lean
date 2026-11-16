module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Thms

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f 0 = a := rfl

/-- The lowest universe and its carrier both fit in a two-level rule budget. -/
theorem bounded_univ_zero : ECtx.JEqB 2 ∅ .nil (.univ 1) (.univ 0) (.univ 0) :=
  .univ (by decide) .nil_ok

/-- Actual bounded formation of the natural numbers needs only the lowest universe. -/
theorem bounded_nats : ECtx.JEqB 1 ∅ .nil (.univ 0) .nats .nats :=
  .nats (by decide) .nil_ok

/-- The common one-level budget supplies every fresh natural-variable context. -/
theorem bounded_nats_context (x : String) :
    ECtx.JEqB 1 ∅ (.cons .nil x .nats) .unit .star .star :=
  .cons_ok (by decide) .nil_ok (by simp [ECtx.dv]) bounded_nats

private theorem bounded_nats_family : ∀ x ∉ (∅ : Finset String),
    ECtx.JEqB 1 ∅ (.cons .nil x .nats) (.univ 0)
      ((.nats : ETm 1).open x) ((.nats : ETm 1).open x) := by
  intro x hx
  simpa only [ETm.open] using ECtx.JEqB.nats (n := 0) (by decide) (bounded_nats_context x)

/-- Every fresh branch of identity beta is an actual one-level derivation. -/
theorem bounded_identity_beta :
    ECtx.JEqB 1 ∅ .nil .nats (.app (.abs .nats (.bv 0)) .zero) .zero := by
  have hb : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 1 ∅ (.cons .nil x .nats)
      ((.nats : ETm 1).open x) ((.bv 0 : ETm 1).open x) ((.bv 0 : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open, lastCases_zero] using
      ECtx.JEqB.var (bounded_nats_context x) (.here _ _ _)
  simpa only [ETm.lst, ETm.castLE, lastCases_zero] using
    ECtx.JEqB.beta_app (n := 0) (L := ∅) (by decide) bounded_nats bounded_nats_family hb
      (.zero .nil_ok)

/-- The Nat step binds the predecessor and increments its recursive result. -/
theorem bounded_increment_step (x : String) :
    ECtx.JEqB 1 ∅ (.cons .nil x .nats) (.arr .nats .nats)
      (.abs .nats (.succ (.bv 0))) (.abs .nats (.succ (.bv 0))) := by
  have hΓ := bounded_nats_context x
  have hNat : ECtx.JEqB 1 ∅ (.cons .nil x .nats) (.univ 0) .nats .nats :=
    .nats (by decide) hΓ
  have hΔ : ∀ y ∉ (ECtx.cons .nil x .nats).dv,
      ECtx.JEqB 1 ∅ ((ECtx.cons .nil x .nats).cons y .nats) .unit .star .star :=
    fun y hy => .cons_ok (by decide) hΓ hy hNat
  apply ECtx.JEqB.abs (n := 0) (L := (ECtx.cons .nil x .nats).dv) (by decide) hNat
  · intro y hy
    simpa only [ETm.wk0, ETm.wkn, ETm.open] using ECtx.JEqB.nats (n := 0) (by decide) (hΔ y hy)
  · intro y hy
    simpa only [ETm.wk0, ETm.wkn, ETm.open, lastCases_zero] using
      ECtx.JEqB.succ (ECtx.JEqB.var (hΔ y hy) (.here _ _ _))

/-- The successor computation has uniformly bounded motive and step premise families. -/
theorem bounded_nat_successor :
    ECtx.JEqB 1 ∅ .nil .nats
      (.natrec .nats (.abs .nats (.succ (.bv 0))) .zero (.succ .zero))
      (.app (.abs .nats (.succ (.bv 0)))
        (.natrec .nats (.abs .nats (.succ (.bv 0))) .zero .zero)) := by
  have hz : ECtx.JEqB 1 ∅ .nil ((.nats : ETm 1).lst .zero) .zero .zero := by
    simpa only [ETm.lst] using ECtx.JEqB.zero (levels := 1) (H := ∅) .nil_ok
  have hs : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 1 ∅ (.cons .nil x .nats)
      (.arr ((.nats : ETm 1).open x) ((.nats : ETm 1).lst (.succ (.fv x))))
      ((.abs .nats (.succ (.bv 0)) : ETm 1).open x)
      ((.abs .nats (.succ (.bv 0)) : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open, ETm.lst, show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      Fin.lastCases_castSucc] using bounded_increment_step x
  simpa only [ETm.lst, show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
    Fin.lastCases_castSucc] using
    ECtx.JEqB.beta_natrec_succ (n := 0) (C := .nats) (s := .abs .nats (.succ (.bv 0)))
      (m := .zero) (L := ∅) (by decide) bounded_nats_family hz hs (.zero .nil_ok)

/-- Erasure yields the actual original beta rule, and the same proof includes at height two. -/
theorem bounded_beta_erases_and_includes :
    ECtx.JEqH ∅ .nil .nats (.app (.abs .nats (.bv 0)) .zero) .zero ∧
      ECtx.JEqB 2 ∅ .nil .nats (.app (.abs .nats (.bv 0)) .zero) .zero :=
  ⟨bounded_identity_beta.forget, bounded_identity_beta.weakenLevels (by decide)⟩

/-- The one-universe system has an inhabited closed data type. -/
theorem ECtx.JEqB.zero_one : ECtx.JEqB 1 ∅ .nil .nats .zero .zero :=
  .zero .nil_ok

/-- The lowest universe has a type in the two-universe system. -/
theorem ECtx.JEqB.univ_zero_two : ECtx.JEqB 2 ∅ .nil (.univ 1) (.univ 0) (.univ 0) :=
  bounded_univ_zero

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
