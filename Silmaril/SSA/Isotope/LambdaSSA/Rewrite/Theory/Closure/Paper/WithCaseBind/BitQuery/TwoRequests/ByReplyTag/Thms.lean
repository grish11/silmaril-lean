module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries

/-! # Exact native comparison for the selected continuations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TwoBitQueries

/-- Replay both typed continuations to their own ordered quotes. -/
theorem packed_replay (p : Program) : p.packed = p.key.packed :=
  TaggedContinuations.packed_replay p

/-- Interpret the original packed arrow in the all-replies trace model. -/
theorem packed_outcomes (p : Program) (guard : Bool) : p.observations guard = p.key.outcomes guard :=
  TaggedContinuations.packed_outcomes p guard

/-- A fixed first history consults exactly the continuation selected by its tag.
The final reply fixes the original payload and ordered exit. -/
theorem observed_history_iff (p q : Program) (guard : Bool) (firstReply secondReply : Reply) :
    p.key.observe guard firstReply secondReply ∈ q.observations guard ↔
      p.key.firstLabel = q.key.firstLabel ∧
        (p.key.arm firstReply.1).label = (q.key.arm firstReply.1).label ∧
        (p.key.arm firstReply.1).query guard firstReply.2 =
          (q.key.arm firstReply.1).query guard firstReply.2 :=
  TaggedContinuations.observed_history_iff p q guard firstReply secondReply

/-- The executable check at a single history predicts membership of the
actual packed trace at every final reply. -/
theorem history_check_iff (p q : Program) (guard : Bool) (firstReply secondReply : Reply) :
    p.key.agreesAt q.key guard firstReply = true ↔
      p.key.observe guard firstReply secondReply ∈ q.observations guard :=
  TaggedContinuations.history_check_iff p q guard firstReply secondReply

theorem packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.key = q.key :=
  TaggedContinuations.packed_eq_iff_key p q

/-- Equality of the all-replies observations is exact on the admitted fragment. -/
theorem observations_iff_packed_eq (p q : Program) :
    (∀ guard, p.observations guard = q.observations guard) ↔ p.packed = q.packed :=
  TaggedContinuations.observations_iff_packed_eq p q

/-- The finite checker decides equality of the original native packed arrows. -/
theorem compare_iff (p q : Program) : p.compare q = true ↔ p.packed = q.packed :=
  TaggedContinuations.compare_iff p q

/-- Following a deterministic policy produces an observation admitted by
the all-replies model. -/
theorem policy_in_observations (p : Program) (policy : Policy) (guard : Bool) :
    p.key.runPolicy policy guard ∈ p.observations guard :=
  TaggedContinuations.policy_in_observations p policy guard

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag.Example
  (reference changed keepLeft)

/-- Exactly one entry of the selected query tables differs. -/
theorem changed_row (tag guard payload : Bool) :
    (reference.key.arm tag).query guard payload ≠ (changed.key.arm tag).query guard payload ↔
      tag = true ∧ guard = true ∧ payload = false :=
  TaggedContinuations.changed_row tag guard payload

/-- Hold the first payload and final reply fixed. The right first tag exposes
the differing query. The left first tag admits the same observation. -/
theorem branch_witness :
    reference.key.observe true (true, false) (true, false) ∈ reference.observations true ∧
    reference.key.observe true (true, false) (true, false) ∉ changed.observations true ∧
    reference.key.observe true (false, false) (true, false) ∈ changed.observations true :=
  TaggedContinuations.branch_witness

theorem branch_ne : reference.packed ≠ changed.packed :=
  TaggedContinuations.branch_ne

theorem checker_regression :
    reference.key.agreesAt changed.key true (false, false) = true ∧
    reference.key.agreesAt changed.key true (true, false) = false ∧
    reference.compare changed = false :=
  TaggedContinuations.checker_regression

/-- A shared policy that chooses a left first reply observes agreement at
both inputs, even for this pair of distinct native arrows. -/
theorem shared_policy_agrees (guard : Bool) :
    reference.key.runPolicy keepLeft guard = changed.key.runPolicy keepLeft guard :=
  TaggedContinuations.shared_policy_agrees guard

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.TwoRequests.ByReplyTag
