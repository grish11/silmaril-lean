module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected

open CategoryTheory
open LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (ReadTree replyInput replyInput_surjective)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

theorem denotation_outcomes_at_assignment_proof (H : Sorts) (L : List Sorts) {n : Nat}
    (p : ReadTree (H :: L) n) (env : Assignment n) :
    ((denotation p).of (replyInput n env)).outcomes = Extensional.programOutcomes H L (witnessed p) env :=
  (p.packedOutcomes_at_assignment env).trans (Extensional.tree_programOutcomes_eq H L p.witnessed env).symm

theorem denotation_eq_iff_pointwise_normal_proof (H : Sorts) (L : List Sorts) {n : Nat}
    (p q : ReadTree (H :: L) n) :
    denotation p = denotation q ↔ ∀ env, (witnessed p).normal env = (witnessed q).normal env := by
  have pointwise (env : Assignment n) :=
    Extensional.programOutcomes_iff_normal H L (witnessed p) (witnessed q) env
  constructor
  · intro eq env
    apply (pointwise env).mp
    rw [← denotation_outcomes_at_assignment_proof H L p, ← denotation_outcomes_at_assignment_proof H L q, eq]
  · intro all
    apply CategoryTheory.Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext x
    obtain ⟨env, rfl⟩ := replyInput_surjective n x
    apply Tagged.outcomes_injective
    rw [denotation_outcomes_at_assignment_proof H L p, denotation_outcomes_at_assignment_proof H L q]
    exact (pointwise env).mpr (all env)

theorem denotation_eq_iff_normal_proof (H : Sorts) (L : List Sorts) (p q : ReadTree (H :: L) 0) :
    denotation p = denotation q ↔ (witnessed p).normal Fin.elim0 = (witnessed q).normal Fin.elim0 :=
  (denotation_eq_iff_pointwise_normal_proof H L p q).trans
    ⟨fun h => h Fin.elim0, fun h env => (show env = Fin.elim0 from funext fun i => i.elim0).symm ▸ h⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected
