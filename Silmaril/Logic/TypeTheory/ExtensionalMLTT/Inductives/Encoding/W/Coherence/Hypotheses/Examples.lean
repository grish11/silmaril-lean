module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Coherence.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

private theorem unit_hyp {Γ : Ctx} : Γ.JEqB 2 (ContextClosure basis) (.univ 0) .unit .unit := by
  apply Ctx.JEqB.hyp
  refine ⟨.nil, hypothesis_present, ?_⟩
  intro y A h
  cases h

/-- The original nullary descriptor uses actual hypothesis leaves for its index and shape. -/
def nullarySourceData : IndexedFormationData nullaryDescription 2 0 .nil (ContextClosure basis) where
  toFormationData := {
    nullaryIndexedFormationData.toFormationData.monoTheory (Set.empty_subset _) with
    index := by exact unit_hyp
    shape := fun _ _ => by simpa only [nullaryDescription, Tm.open] using unit_hyp }
  next x hx y hy p hp := (nullaryIndexedFormationData.next x hx y hy p hp).mono (Set.empty_subset _)

/-- An independently typed actual raw leaf inhabits the nonempty source theory. -/
theorem nullary_rawLeaf_typing : Ctx.nil.JEqB 2 (ContextClosure basis) nullaryDescription.raw
    nullaryRawLeaf nullaryRawLeaf :=
  WEncoding.Terms.nullaryRawLeaf_typing.mono (Set.empty_subset _)

theorem nullary_root_typing : Ctx.nil.JEqB 2 (ContextClosure basis) .unit
    (nullaryDescription.root nullaryRawLeaf) (nullaryDescription.root nullaryRawLeaf) :=
  root_typing_of_hypotheses basis_structural nullarySourceData.toFormationData nullary_rawLeaf_typing

theorem nullary_coherence_formation : Ctx.nil.JEqB 2 (ContextClosure basis) (.univ 0)
    (nullaryDescription.coherence 0 nullaryRawLeaf) (nullaryDescription.coherence 0 nullaryRawLeaf) :=
  coherence_formation_of_hypotheses basis_structural nullarySourceData nullary_rawLeaf_typing

theorem nullary_fibre_formation : Ctx.nil.JEqB 2 (ContextClosure basis) (.univ 0)
    (nullaryDescription.fibre 0 .star) (nullaryDescription.fibre 0 .star) :=
  fibre_formation_of_hypotheses basis_structural nullarySourceData .nil_ok

theorem nullary_compiledRoot_typing : Ctx.nil.JEqB 2 (ContextClosure basis) .unit
    (nullaryDescription.compiledRoot nullaryRawLeaf) (nullaryDescription.compiledRoot nullaryRawLeaf) := by
  have hcompiled : Ctx.nil.JEqB 2 (ContextClosure basis) nullaryDescription.compiledRaw
      nullaryRawLeaf nullaryRawLeaf :=
    .conv (n := 0) (by decide)
      (compiledRaw_beta_of_hypotheses basis_structural nullarySourceData.toFormationData).symm nullary_rawLeaf_typing
  exact compiledRoot_typing_of_hypotheses basis_structural.weakening nullarySourceData.toFormationData hcompiled

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples
