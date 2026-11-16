module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.Examples

private theorem last_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- A dependent function returns a reflexivity proof at its supplied natural number. -/
def reflexivityFunction : ETm 0 := .abs .nats (.refl (.bv 0))

def reflexivityCarrier : ETm 0 := .pi .nats (.id .nats (.bv 0) (.bv 0))

private theorem family_formation : ∀ x ∉ (∅ : Finset String),
    ECtx.JEqH ∅ (ECtx.nil.cons x .nats) (.univ 0)
      ((ETm.id .nats (.bv 0) (.bv 0)).open x)
      ((ETm.id .nats (.bv 0) (.bv 0)).open x) := by
  intro x _
  have hc : ECtx.JEqH ∅ (ECtx.nil.cons x .nats) .unit .star .star :=
    .cons_ok .nil_ok (by simp [ECtx.dv]) (ECtx.JEqH.nats (n := 0) .nil_ok)
  have hv : ECtx.JEqH ∅ (ECtx.nil.cons x .nats) .nats (.fv x) (.fv x) := .var hc (.here ..)
  simpa only [ETm.open, last_zero] using ECtx.JEqH.id (n := 0) (.nats hc) hv hv

theorem reflexivity_typed : ECtx.JEqH ∅ .nil reflexivityCarrier reflexivityFunction reflexivityFunction := by
  apply ECtx.JEqH.abs (L := ∅) (ECtx.JEqH.nats (n := 0) .nil_ok) family_formation
  intro x _
  have hc : ECtx.JEqH ∅ (ECtx.nil.cons x .nats) .unit .star .star :=
    .cons_ok .nil_ok (by simp [ECtx.dv]) (ECtx.JEqH.nats (n := 0) .nil_ok)
  simpa only [ETm.open, last_zero] using ECtx.JEqH.refl (ECtx.JEqH.var hc (ECtx.Lookup.here ..))

/-- Eta equality retains the genuinely argument-dependent identity codomain. -/
theorem dependent_eta : ECtx.JEqH ∅ .nil reflexivityCarrier
    (.abs .nats (.app reflexivityFunction.wk0 (.bv 0))) reflexivityFunction :=
  ECtx.JEqH.function_eta (ECtx.JEqH.nats (n := 0) .nil_ok) family_formation reflexivity_typed

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.Examples
