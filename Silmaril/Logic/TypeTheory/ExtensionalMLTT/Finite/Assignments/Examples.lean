module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Examples

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- A real one-name assignment replaces the source natural variable by zero at budget one. -/
theorem bounded_assigned_successor : ECtx.JEqB 1 ∅ .nil .nats (.succ .zero) (.succ .zero) := by
  have hv : ECtx.JEqB 1 ∅ .nil (ETm.nats.fmap ETm.fv) .zero .zero := by
    simpa only [ETm.fmap_id] using ECtx.JEqB.zero (levels := 1) (H := ∅) .nil_ok
  have e : ECtx.AssignmentB 1 (Function.update ETm.fv "n" .zero) (.cons .nil "n" .nats) .nil :=
    ECtx.AssignmentB.update (ECtx.AssignmentB.identity .nil_ok)
      (by simp [ECtx.typeFvs]) (by simp [ETm.fvs]) hv
  have hs : ETm.Supported (Function.update ETm.fv "n" .zero) (insert "n" ∅) :=
    ETm.Supported.update ETm.fv (fun _ _ => rfl) "n" .zero
  have hbody : ECtx.JEqB 1 ∅ (.cons .nil "n" .nats) .nats
      (.succ (.fv "n")) (.succ (.fv "n")) :=
    .succ (.var (bounded_nats_context "n") (.here _ _ _))
  simpa only [ETm.fmap, Function.update_self, ETm.castLE_refl] using
    hbody.assign _ _ hs e .nil_ok

/-- The actual nonconstant successor binder instantiates without increasing its level count. -/
theorem bounded_instantiated_successor : ECtx.JEqB 1 ∅ .nil .nats (.succ .zero) (.succ .zero) := by
  have hbody : ∀ y ∉ (∅ : Finset String), ECtx.JEqB 1 ∅ (.cons .nil y .nats)
      ((.nats : ETm 1).open y) ((.succ (.bv 0) : ETm 1).open y)
      ((.succ (.bv 0) : ETm 1).open y) := by
    intro y hy
    simpa only [ETm.open, lastCases_zero] using
      ECtx.JEqB.succ (ECtx.JEqB.var (bounded_nats_context y) (.here _ _ _))
  simpa only [ETm.lst, ETm.castLE, lastCases_zero] using
    ECtx.JEqB.instantiate (v := .zero) .nil_ok (.zero .nil_ok) hbody

/-- Beta computes an actual type equality, using a two-level proof budget throughout. -/
theorem bounded_computed_nats :
    ECtx.JEqB 2 ∅ .nil (.univ 0) (.app (.abs .unit .nats) .star) .nats := by
  have hUnit : ECtx.JEqB 2 ∅ .nil (.univ 1) .unit .unit := .unit (by decide) .nil_ok
  have hΓ : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 2 ∅ (.cons .nil x .unit) .unit .star .star :=
    fun x hx => .cons_ok (by decide) .nil_ok (by simp [ECtx.dv]) hUnit
  have hB : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 2 ∅ (.cons .nil x .unit) (.univ 1)
      ((.univ 0 : ETm 1).open x) ((.univ 0 : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using ECtx.JEqB.univ (n := 0) (by decide) (hΓ x hx)
  have hb : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 2 ∅ (.cons .nil x .unit)
      ((.univ 0 : ETm 1).open x) ((.nats : ETm 1).open x) ((.nats : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using ECtx.JEqB.nats (n := 0) (by decide) (hΓ x hx)
  simpa only [ETm.lst] using
    ECtx.JEqB.beta_app (n := 1) (L := ∅) (by decide) hUnit hB hb (.nil_ok)

/-- Actual type equality changes a declaration while retaining the original computed carrier. -/
theorem bounded_computed_context_change :
    ECtx.JEqB 2 ∅ (.cons .nil "n" .nats)
      (.app (.abs .unit .nats) .star) (.fv "n") (.fv "n") := by
  have hA : ECtx.JEqB 2 ∅ .nil (.univ 0)
      (.app (.abs .unit .nats) .star) (.app (.abs .unit .nats) .star) :=
    .trans bounded_computed_nats (.symm bounded_computed_nats)
  have hΓ : ECtx.JEqB 2 ∅ (.cons .nil "n" (.app (.abs .unit .nats) .star)) .unit .star .star :=
    .cons_ok (by decide) .nil_ok (by simp [ECtx.dv]) hA
  exact ECtx.JEqB.changeLast .nil_ok (by simp [ECtx.dv]) (by decide)
    bounded_computed_nats (.var hΓ (.here _ _ _))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
