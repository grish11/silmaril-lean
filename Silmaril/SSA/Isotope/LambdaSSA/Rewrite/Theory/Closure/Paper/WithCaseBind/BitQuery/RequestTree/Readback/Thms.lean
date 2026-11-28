module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReadback

/-! # Native comparison at the original packed arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Every successful readback proves equality in unchanged Paper at the
literal packing of the supplied region. -/
theorem Candidate.packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) : p.packed = t.defaultPacked :=
  BitQueryTreeReadback.packed_eq h

theorem Candidate.observations_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) (guard : Bool) : p.observations guard = t.observations guard :=
  BitQueryTreeReadback.observations_eq h guard

theorem eq_iff_key {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key :=
  BitQueryTreeReadback.eq_iff_key hp hq

theorem eq_iff_observations {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ ∀ guard, p.observations guard = q.observations guard :=
  BitQueryTreeReadback.eq_iff_observations hp hq

theorem compare_equal {fuel : Nat} {p q : Candidate} (h : Readback.compare fuel p q = .equal) :
    p.packed = q.packed :=
  BitQueryTreeReadback.compare_equal h

/-- Once both original candidates are admitted, equality has a decision. -/
theorem compare_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    Readback.compare fuel p q = .equal ↔ p.packed = q.packed :=
  BitQueryTreeReadback.compare_equal_iff hp hq

/-- The ordered history is possible for one original arrow and impossible
for the other in the existing validated tagged model. -/
theorem compare_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard :=
  BitQueryTreeReadback.compare_different h

theorem compare_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) : p.packed ≠ q.packed :=
  BitQueryTreeReadback.compare_different_ne h

theorem compare_diff_of_ne {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) (hne : p.packed ≠ q.packed) :
    ∃ w, Readback.compare fuel p q = .different w :=
  BitQueryTreeReadback.compare_diff_of_ne hp hq hne

namespace Example

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

theorem forward_typed (right : Bool) : ValueBranches [Bit] (forward right) Exits :=
  BitQueryTreeReadback.Example.forward_typed right

theorem backward_typed (right : Bool) : ValueBranches [Bit] (backward right) Exits :=
  BitQueryTreeReadback.Example.backward_typed right

@[expose] def first : Candidate := ⟨forward false, forward_typed false⟩

@[expose] def renumbered : Candidate := ⟨backward false, backward_typed false⟩

@[expose] def otherExit : Candidate := ⟨backward true, backward_typed true⟩

@[expose] def unsupported : Candidate := ⟨variableQuery, call_typed false (.var (i := 0) rfl)⟩

theorem reads_first : first.read 16 = some (expected false) := rfl

theorem reads_renumbered : renumbered.read 16 = some (expected false) := rfl

theorem reads_otherExit : otherExit.read 16 = some (expected true) := rfl

theorem compare_renumbered : Readback.compare 16 first renumbered = .equal := rfl

theorem packed_renumbered : first.packed = renumbered.packed := compare_equal compare_renumbered

theorem compare_ordered_exit : Readback.compare 16 first otherExit = .different witness := rfl

theorem separated_ordered_exit :
    witness.history.observation ∈ first.observations witness.guard ∧
      witness.history.observation ∉ otherExit.observations witness.guard :=
  compare_different (fuel := 16) (p := first) (q := otherExit) (w := witness) compare_ordered_exit

theorem variable_query_unknown : Readback.compare 16 first unsupported = .unknown := rfl

end Example

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)

theorem readQuery_typed {written : Bool} {n : Nat} {arg : Tm signature.Instr} {query : Expr n}
    (h : readQuery written n arg = some query) : Tm.HasType (Live n) arg Bit :=
  BitQueryTreeReadback.readQuery_typed h

/-- Readback with variables preserves the actual opcode argument at the original
packed endpoint in unchanged Paper. -/
theorem Candidate.packed_eq_with_variables {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithVariables fuel = some t) : p.packed = t.writtenPacked :=
  BitQueryTreeReadback.written_packed_eq h

theorem Candidate.observations_eq_with_variables {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithVariables fuel = some t) (guard : Bool) : p.observations guard = t.observations guard :=
  BitQueryTreeReadback.written_observations_eq h guard

/-- The ordered key recovers the exact literal-or-variable tree. -/
theorem eq_of_direct_key {n : Nat} {t u : Tree n} (ht : Direct t) (hu : Direct u)
    (h : t.key = u.key) : t = u :=
  BitQueryTreeReadback.eq_of_direct_key ht hu h

/-- The original quotation key is complete on the admitted literal-or-variable
grammar. Key equality identifies the original variable, including its scope. -/
theorem eq_iff_key_with_variables {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithVariables fuel = some t) (hq : q.readWithVariables fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key :=
  BitQueryTreeReadback.written_eq_iff_key hp hq

theorem compare_with_variables_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithVariables fuel = some t) (hq : q.readWithVariables fuel = some u) :
    Readback.compareWithVariables fuel p q = .equal ↔ p.packed = q.packed :=
  BitQueryTreeReadback.compare_written_equal_iff hp hq

theorem compare_with_variables_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithVariables fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard :=
  BitQueryTreeReadback.compare_written_different h

theorem compare_with_variables_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithVariables fuel p q = .different w) : p.packed ≠ q.packed :=
  BitQueryTreeReadback.compare_written_different_ne h

namespace VariableExample

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Assignment)

theorem numbered_typed (renumbered altered : Bool) : ValueBranches [Bit] (numbered renumbered altered) Exits :=
  BitQueryTreeReadback.VariableExample.numbered_typed renumbered altered

theorem effectful_query_typed : ValueBranches [Bit] effectfulQuery Exits :=
  BitQueryTreeReadback.VariableExample.effectful_query_typed

@[expose] def program (renumbered altered : Bool) : Candidate :=
  ⟨numbered renumbered altered, numbered_typed renumbered altered⟩

@[expose] def unsupported : Candidate := ⟨effectfulQuery, effectful_query_typed⟩

theorem reads_numbered : (program false false).readWithVariables 16 = some (expected false) := rfl

theorem reads_renumbered : (program true false).readWithVariables 16 = some (expected false) := rfl

theorem reads_altered : (program true true).readWithVariables 16 = some (expected true) := rfl

theorem same_packed : (program false false).packed = (program true false).packed :=
  (Candidate.packed_eq_with_variables reads_numbered).trans
    (Candidate.packed_eq_with_variables reads_renumbered).symm

/-- The query changes only in the right continuation, and exactly when the
forwarded reply differs from the retained original guard. -/
theorem mismatch_iff (guard tag payload : Bool) :
    let env := Assignment.push (fun _ : Fin 1 => guard) payload
    env (querySlot false tag) ≠ env (querySlot true tag) ↔ tag = true ∧ payload ≠ guard := by
  cases guard <;> cases tag <;> cases payload <;> decide

theorem compare_query : Readback.compareWithVariables 16 (program false false) (program true true) =
    .different witness := rfl

theorem separates_query :
    witness.history.observation ∈ (program false false).observations witness.guard ∧
      witness.history.observation ∉ (program true true).observations witness.guard :=
  compare_with_variables_different (fuel := 16) (p := program false false)
    (q := program true true) (w := witness) compare_query

theorem effectful_query_unknown :
    Readback.compareWithVariables 16 (program false false) unsupported = .unknown := rfl

end VariableExample

/-- Successful decision readback proves equality in unchanged Paper at the
original packed endpoint and the guarded tree used by default quotation. -/
theorem Candidate.packed_eq_with_decisions {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithDecisions fuel = some t) : p.packed = t.defaultPacked :=
  BitQueryTreeReadback.packed_eq_decision h

/-- Different query expressions may have the same key. Completeness uses
native quotation, including contextual case expansion on each live slot. -/
theorem eq_iff_key_with_decisions {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithDecisions fuel = some t) (hq : q.readWithDecisions fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key :=
  BitQueryTreeReadback.decision_eq_iff_key hp hq

theorem compare_with_decisions_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithDecisions fuel = some t) (hq : q.readWithDecisions fuel = some u) :
    Readback.compareWithDecisions fuel p q = .equal ↔ p.packed = q.packed :=
  BitQueryTreeReadback.compare_decision_equal_iff hp hq

theorem compare_with_decisions_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithDecisions fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard :=
  BitQueryTreeReadback.compare_decision_different h

theorem compare_with_decisions_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithDecisions fuel p q = .different w) : p.packed ≠ q.packed :=
  BitQueryTreeReadback.compare_decision_different_ne h

namespace DecisionExample

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Assignment)

theorem numbered_typed (renumbered : Bool) (shape : Shape) :
    ValueBranches [Bit] (numbered renumbered shape) Exits :=
  BitQueryTreeReadback.DecisionExample.numbered_typed renumbered shape

theorem term_case_typed : ValueBranches [Bit] termCase Exits :=
  BitQueryTreeReadback.DecisionExample.term_case_typed

@[expose] def program (renumbered : Bool) (shape : Shape) : Candidate :=
  ⟨numbered renumbered shape, numbered_typed renumbered shape⟩

@[expose] def termOperand : Candidate := ⟨termCase, term_case_typed⟩

theorem reads_plain : (program false .plain).readWithDecisions 16 = some (expected .plain) := rfl

theorem reads_redundant : (program true .redundant).readWithDecisions 16 = some (expected .redundant) := rfl

theorem reads_changed : (program true .changed).readWithDecisions 16 = some (expected .changed) := rfl

theorem distinct_readbacks : expected .plain ≠ expected .redundant :=
  BitQueryTreeReadback.DecisionExample.expected_ne

theorem same_key : (expected .plain).key = (expected .redundant).key := rfl

theorem same_packed : (program false .plain).packed = (program true .redundant).packed :=
  (eq_iff_key_with_decisions reads_plain reads_redundant).mpr same_key

/-- Only the right first reply with true payload and a false caller
Bit changes the second query. -/
theorem mismatch_iff (guard tag payload : Bool) :
    let env := Assignment.push (fun _ : Fin 1 => guard) payload
    (selectedQuery .plain tag).eval env ≠ (selectedQuery .changed tag).eval env ↔
      tag = true ∧ payload = true ∧ guard = false := by
  cases guard <;> cases tag <;> cases payload <;> decide

theorem compare_one_assignment :
    Readback.compareWithDecisions 16 (program false .plain) (program true .changed) = .different witness := rfl

theorem separates_one_assignment :
    witness.history.observation ∈ (program false .plain).observations witness.guard ∧
      witness.history.observation ∉ (program true .changed).observations witness.guard :=
  compare_with_decisions_different (fuel := 16) (p := program false .plain)
    (q := program true .changed) (w := witness) compare_one_assignment

/-- The focused operand-beta obligation is sufficient at the literal packed
representative of the well-typed term-level example. -/
theorem term_case_packed_of (beta : CaseOperandBeta) : termOperand.packed = quotedTermCase.defaultPacked :=
  BitQueryTreeReadback.DecisionExample.term_case_packed_of beta

theorem pure_term_case_unknown :
    Readback.compareWithDecisions 16 (program false .plain) termOperand = .unknown := rfl

theorem effectful_operand_unknown :
    Readback.compareWithDecisions 16 (program false .plain) VariableExample.unsupported = .unknown := rfl

end DecisionExample

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
