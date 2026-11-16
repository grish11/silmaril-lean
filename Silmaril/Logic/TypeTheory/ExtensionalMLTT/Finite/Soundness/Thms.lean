module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Soundness.Defs
public import Silmaril.Logic.SetTheory.Universes.Finite
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FiniteSoundness

public section

/-!
# Actual bounded extensional MLTT soundness in finite set towers

Every rule of `JEqB levels H` is valid in an actual `FiniteTower levels` when
its hypothesis judgments are valid in that tower. The induction uses only the
recorded in-range closure and successor-membership laws. Hypotheses may have
arbitrary syntax; their semantic validity is explicit. No infinite hierarchy
or global soundness certificate is assumed.

Actual finite model supplies exclude closed Empty inhabitants at the same
rule budget. The concrete supplies at heights one, two and three live in
successively larger Lean set carriers.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open Silmaril.Logic.SetTheory

universe u

/-- Every actual bounded target rule preserves validity in its supplied finite tower. -/
theorem ECtx.JEqB.sound {levels : ℕ} (T : FiniteTower.{u} levels) {H : Set EJdg}
    (hH : ∀ j ∈ H, EJdg.ValidIn T.U j) {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : EJdg.ValidIn T.U ⟨Γ, A, a, b⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FiniteSoundness.sound T hH h

/-- Empty-theory actual bounded proofs are valid in every supplied finite tower. -/
theorem ECtx.JEqB.sound_empty {levels : ℕ} (T : FiniteTower.{u} levels)
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels ∅ Γ A a b) :
    EJdg.ValidIn T.U ⟨Γ, A, a, b⟩ := h.sound T (fun _ hj => False.elim hj)

/-- A supplied finite target tower excludes any closed actual bounded Empty equality. -/
theorem ECtx.JEqB.no_closed_empty {levels : ℕ} (T : FiniteTower.{u} levels) {a b : ETm 0} :
    ¬ ECtx.JEqB levels ∅ .nil .empty a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FiniteSoundness.no_empty T

/-- A supplied finite tower excludes a closed inhabitant of Empty. -/
theorem ECtx.JEqB.consistent {levels : ℕ} (T : FiniteTower.{u} levels) {a : ETm 0} :
    ¬ ECtx.JEqB levels ∅ .nil .empty a a :=
  ECtx.JEqB.no_closed_empty T

/-- Fixed-budget consistency from the supplied finite set model. -/
theorem ECtx.JEqB.consistent_of_tower (levels : ℕ) [HasFiniteTower.{u} levels] {a : ETm 0} :
    ¬ ECtx.JEqB levels ∅ .nil .empty a a :=
  ECtx.JEqB.consistent (HasFiniteTower.tower levels)

/-- One available universe is consistent in the concrete next-carrier model. -/
theorem ECtx.JEqB.consistent_one {a : ETm 0} : ¬ ECtx.JEqB 1 ∅ .nil .empty a a :=
  ECtx.JEqB.consistent FiniteTower.one.{0}

/-- Two available universes are consistent in the concrete two-step model. -/
theorem ECtx.JEqB.consistent_two {a : ETm 0} : ¬ ECtx.JEqB 2 ∅ .nil .empty a a :=
  ECtx.JEqB.consistent FiniteTower.two.{0}

/-- Three available universes are consistent in the concrete three-step model. -/
theorem ECtx.JEqB.consistent_three {a : ETm 0} : ¬ ECtx.JEqB 3 ∅ .nil .empty a a :=
  ECtx.JEqB.consistent FiniteTower.three.{0}

namespace Finite

/-- An actual finite model supply establishes Empty consistency of the bounded target rules. -/
theorem bounded_no_closed_empty (levels : ℕ) [HasFiniteTower.{u} levels] {a b : ETm 0} :
    ¬ ECtx.JEqB levels ∅ .nil .empty a b :=
  ECtx.JEqB.no_closed_empty (HasFiniteTower.tower.{u} levels)

/-- Concrete one-level target consistency uses the model in the next Lean carrier. -/
theorem bounded_no_closed_empty_one {a b : ETm 0} : ¬ ECtx.JEqB 1 ∅ .nil .empty a b :=
  bounded_no_closed_empty.{1} 1

/-- Concrete two-level target consistency uses a model two Lean carriers higher. -/
theorem bounded_no_closed_empty_two {a b : ETm 0} : ¬ ECtx.JEqB 2 ∅ .nil .empty a b :=
  bounded_no_closed_empty.{2} 2

/-- Concrete three-level target consistency uses a model three Lean carriers higher. -/
theorem bounded_no_closed_empty_three {a b : ETm 0} : ¬ ECtx.JEqB 3 ∅ .nil .empty a b :=
  bounded_no_closed_empty.{3} 3

end Finite

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
