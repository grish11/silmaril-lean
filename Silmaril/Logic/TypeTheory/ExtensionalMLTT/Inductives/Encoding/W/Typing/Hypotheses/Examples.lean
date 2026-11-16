module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Typing.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- A nonempty theory with an independently derivable original hypothesis. -/
def indexHypothesis : Jdg := ⟨.nil, .univ 0, .unit, .unit⟩

def basis : Set Jdg := {indexHypothesis}

theorem hypothesis_present : indexHypothesis ∈ basis := rfl

/-- The theory leaves are realized by actual empty-theory proofs at the same cap. -/
theorem basis_realized {j : Jdg} (hj : j ∈ basis) : j.Γ.JEqB 2 ∅ j.A j.a j.b := by
  have heq : j = indexHypothesis := hj
  subst j
  exact .unit (n := 0) (by decide) .nil_ok

/-- The index field deliberately uses the original theory leaf. -/
def sourceData : FormationData nullaryDescription 2 0 .nil basis where
  bound := by decide
  names := ∅
  declared := by simp [Ctx.dv]
  context := .nil_ok
  index := .hyp hypothesis_present
  shape x _ := by
    have hΓ : (Ctx.nil.cons x .unit).JEqB 2 basis .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.hyp hypothesis_present)
    simpa only [nullaryDescription, Tm.open] using Ctx.JEqB.unit (n := 0) (by decide) hΓ
  position x _ y hy := by
    have hΓ : (Ctx.nil.cons x .unit).JEqB 2 basis .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.hyp hypothesis_present)
    have hΔ : ((Ctx.nil.cons x .unit).cons y .unit).JEqB 2 basis .unit .star .star :=
      .cons_ok (n := 0) (by decide) hΓ (by simpa only [Ctx.dv] using hy) (.unit (n := 0) (by decide) hΓ)
    simpa only [nullaryDescription, Tm.open] using Ctx.JEqB.empty (n := 0) (by decide) hΔ

/-- The arbitrary-theory carrier proof uses the constructive context closure. -/
theorem raw_formed : Ctx.nil.JEqB 2 (ContextClosure basis) (.univ 0)
    nullaryDescription.compiledRaw nullaryDescription.compiledRaw :=
  compiledRaw_formation_contextClosure sourceData

theorem original_hypothesis_extended (x : String) :
    (Ctx.nil.cons x .unit).JEqB 2 (ContextClosure basis) (.univ 0) .unit .unit := by
  have e : Ctx.nil.LookupLE (Ctx.nil.cons x .unit) := by
    intro y A h
    cases h
  have hΔ : (Ctx.nil.cons x .unit).JEqB 2 (ContextClosure basis) .unit .star .star :=
    .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.unit (n := 0) (by decide) .nil_ok)
  exact Ctx.JEqB.weaken_contextClosure (.hyp hypothesis_present) e hΔ

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples
