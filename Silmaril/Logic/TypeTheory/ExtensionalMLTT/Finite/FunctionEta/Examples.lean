module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.FunctionEta.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.Examples

public section
namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.FiniteFunctionEtaExamples
open FunctionEta.Examples

private theorem last_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem family_formation {levels : ℕ} (hn : 0 < levels) : ∀ x ∉ (∅ : Finset String),
    ECtx.JEqB levels ∅ (ECtx.nil.cons x .nats) (.univ 0)
      ((ETm.id .nats (.bv 0) (.bv 0)).open x)
      ((ETm.id .nats (.bv 0) (.bv 0)).open x) := by
  intro x _
  have hc : ECtx.JEqB levels ∅ (ECtx.nil.cons x .nats) .unit .star .star :=
    .cons_ok hn .nil_ok (by simp [ECtx.dv]) (.nats hn .nil_ok)
  have hv : ECtx.JEqB levels ∅ (ECtx.nil.cons x .nats) .nats (.fv x) (.fv x) := .var hc (.here ..)
  simpa only [ETm.open, last_zero] using ECtx.JEqB.id hn (.nats hn hc) hv hv

/-- A genuinely dependent function is checked at every positive finite budget. -/
theorem reflexivity_typed {levels : ℕ} (hn : 0 < levels) :
    ECtx.JEqB levels ∅ .nil reflexivityCarrier reflexivityFunction reflexivityFunction := by
  apply ECtx.JEqB.abs (L := ∅) hn (.nats hn .nil_ok) (family_formation hn)
  intro x _
  have hc : ECtx.JEqB levels ∅ (ECtx.nil.cons x .nats) .unit .star .star :=
    .cons_ok hn .nil_ok (by simp [ECtx.dv]) (.nats hn .nil_ok)
  simpa only [ETm.open, last_zero] using ECtx.JEqB.refl (ECtx.JEqB.var hc (ECtx.Lookup.here ..))

/-- Eta keeps the argument-dependent identity codomain and needs only budget one. -/
theorem dependent_eta_one : ECtx.JEqB 1 ∅ .nil reflexivityCarrier
    (.abs .nats (.app reflexivityFunction.wk0 (.bv 0))) reflexivityFunction :=
  ECtx.JEqB.function_eta (by decide) (.nats (by decide) .nil_ok)
    (family_formation (by decide)) (reflexivity_typed (by decide))

/-- The equality relates different syntax, so the eta regression is substantive. -/
example : (ETm.abs .nats (.app reflexivityFunction.wk0 (.bv 0)) : ETm 0) ≠ reflexivityFunction := by
  intro same
  have body : ETm.app reflexivityFunction.wk0 (.bv 0) = (ETm.refl (.bv 0) : ETm 1) :=
    (ETm.abs.inj same).2
  cases body

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.FiniteFunctionEtaExamples
