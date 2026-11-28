module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Reflection

/-! # Reflection for the selected packed arrows in the validated trace model -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected

open CategoryTheory
open LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (ReadTree replyInput)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => Kleisli.J (m := Trace)

/-- The assignment-indexed equation uses the same packed LetCase program
as the selected compiler's agreement theorem. -/
theorem witnessed_program (H : Sorts) (L : List Sorts) (p : ReadTree (H :: L) 0) :
    Extensional.program H L (witnessed p) = Finite.program H L p.witnessed :=
  rfl

/-- At each point of the retained product, compare the actual selected
arrow with the open packed LetCase program at the same assignment. -/
theorem denotation_outcomes_at_assignment (H : Sorts) (L : List Sorts) {n : Nat}
    (p : ReadTree (H :: L) n) (env : Assignment n) :
    ((denotation p).of (replyInput n env)).outcomes = Extensional.programOutcomes H L (witnessed p) env :=
  denotation_outcomes_at_assignment_proof H L p env

theorem denotation_at_assignment (H : Sorts) (L : List Sorts) {n : Nat}
    (p : ReadTree (H :: L) n) (env : Assignment n) :
    (denotation p).of (replyInput n env) =
      Kleisli.run model (Extensional.program H L (witnessed p)).toLetCase.2
        (boundEnv Kleisli.value (CommonRequest.packedAssignment n env)) :=
  Tagged.outcomes_injective (denotation_outcomes_at_assignment H L p env)

/-- Scope zero has one input. Both computations use the original ordered exit list. -/
theorem denotation_at_unit (H : Sorts) (L : List Sorts) (p : ReadTree (H :: L) 0) :
    (denotation p).of PUnit.unit =
      Kleisli.run model (Extensional.program H L (witnessed p)).toLetCase.2
        (boundEnv Kleisli.value (CommonRequest.packedAssignment 0 Fin.elim0)) :=
  p.denote_agrees H L

/-- Equality of the actual packed Kleisli arrows is equality of the witnessed
normal forms at the empty assignment. -/
theorem denotation_eq_iff_normal (H : Sorts) (L : List Sorts) (p q : ReadTree (H :: L) 0) :
    denotation p = denotation q ↔ (witnessed p).normal Fin.elim0 = (witnessed q).normal Fin.elim0 :=
  denotation_eq_iff_normal_proof H L p q

/-- Assignments exhaust the native product, so pointwise normal equality
determines the actual open Kleisli arrows. -/
theorem denotation_eq_iff_pointwise_normal (H : Sorts) (L : List Sorts) {n : Nat}
    (p q : ReadTree (H :: L) n) :
    denotation p = denotation q ↔ ∀ env, (witnessed p).normal env = (witnessed q).normal env :=
  denotation_eq_iff_pointwise_normal_proof H L p q

theorem denotation_eq_iff_sat (H : Sorts) (L : List Sorts) {n : Nat} (p q : ReadTree (H :: L) n) :
    denotation p = denotation q ↔ (grammarRoom J signature).Sat separator (equation H L p q) :=
  (denotation_eq_iff_pointwise_normal H L p q).trans
    (Extensional.separator_sat_iff_normal H L (witnessed p) (witnessed q)).symm

/-- The fixed separator reflects equality of the open packed arrows to
native LetCase derivability on their actual witnesses, in both directions. -/
theorem denotation_eq_iff_derivable (H : Sorts) (L : List Sorts) {n : Nat} (p q : ReadTree (H :: L) n) :
    denotation p = denotation q ↔ Derivable false (equation H L p q) :=
  (denotation_eq_iff_sat H L p q).trans (Extensional.separator_sat_iff_native H L (witnessed p) (witnessed q))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected
