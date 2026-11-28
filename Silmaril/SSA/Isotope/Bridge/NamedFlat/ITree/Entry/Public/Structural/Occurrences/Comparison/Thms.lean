module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.RegisterRename.Thms

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V W K : Type 1} [DecidableEq V] [DecidableEq W] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

/-- The executable gate tests only the two exact packet equalities. The
dispatcher admissions are already recorded in the structural entries. -/
theorem StructuralEntry.checkOccurrenceComparison?_isSome_iff :
    (left.checkOccurrenceComparison? right).isSome = true ↔
      left.entry.context.get left.provenance.slot = inputType ∧
      right.entry.context.get right.provenance.slot = rightType := by
  by_cases l : left.entry.context.get left.provenance.slot = inputType <;>
    by_cases r : right.entry.context.get right.provenance.slot = rightType <;>
    simp [StructuralEntry.checkOccurrenceComparison?, l, r]

theorem StructuralEntry.checkOccurrenceComparison?_isSome_rename (names : V ↪ W) :
    ((left.rename names).checkOccurrenceComparison? (right.rename names)).isSome =
      (left.checkOccurrenceComparison? right).isSome := by
  rw [Bool.eq_iff_iff, (left.rename names).checkOccurrenceComparison?_isSome_iff,
    left.checkOccurrenceComparison?_isSome_iff, left.occurrencePacketType_rename, right.occurrencePacketType_rename]

variable {left right} (checked : OccurrenceComparison left right)

namespace OccurrenceComparison

/-- At a jointly decoded named store, the sentence is precisely the one
for the original RTL runners, with the same ordered exits and live-outs. -/
theorem sentence_eq_original (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
    (ha : left.seed? initial = some a) (hb : right.seed? initial = some b) :
    checked.sentence a b = left.refinementSentenceAt right initial :=
  (checked.leftAdmission.refinementSentence_eq_versioned checked.rightAdmission initial a b ha hb).trans
    (left.versionedRefinementSentence_eq right initial)

/-- The two checked comparisons use the same sentence at corresponding seeds. -/
theorem sentence_rename (names : V ↪ W)
    (renamed : OccurrenceComparison (left.rename names) (right.rename names))
    (a : Denote inputType) (b : Denote rightType) :
    renamed.sentence a b = checked.sentence a b :=
  checked.leftAdmission.refinementSentence_rename checked.rightAdmission names
    renamed.leftAdmission renamed.rightAdmission a b

variable [DecidableEq F]

theorem fromStore?_eq_none_iff (initial : V → Value Atom) :
    checked.fromStore? initial = none ↔ left.seed? initial = none ∨ right.seed? initial = none := by
  cases l : left.seed? initial <;> cases r : right.seed? initial <;>
    simp [fromStore?, StructuralEntry.refinementFromStore?, l, r]

/-- A returned Boolean is exact for the two decoded occurrence starts and
all shared reply policies. Both seeds have to decode even for rejection. -/
theorem fromStore?_eq_some_iff (initial : V → Value Atom) (verdict : Bool) :
    checked.fromStore? initial = some verdict ↔
      ∃ (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a ∧ right.seed? initial = some b ∧
        (verdict = true ↔ ∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (checked.sentence a b)) :=
  checked.leftAdmission.refinementFromStore?_eq_some_iff checked.rightAdmission initial verdict

/-- The finite comparison is exact over the whole jointly decoded domain. -/
theorem overCaptures_iff_valid :
    checked.overCaptures.verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a → right.seed? initial = some b →
        ∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (checked.sentence a b) :=
  checked.leftAdmission.refinementOverCaptures_iff_valid checked.rightAdmission

theorem overCaptures_hasVerdict : checked.overCaptures.verdict.isSome = true :=
  left.refinementOverCaptures_hasVerdict right

theorem overCaptures_emptyDomain_iff :
    checked.overCaptures.emptyDomain = true ↔ ¬ ∃ initial,
      (left.seed? initial).isSome = true ∧ (right.seed? initial).isSome = true := by
  rw [show checked.overCaptures = left.refinementOverCaptures right from rfl,
    left.refinementOverCaptures_emptyDomain_iff right]
  simp only [Option.isSome_iff_exists, StructuralEntry.seed?, decodeSeed?_eq_some_iff]

theorem counterexample?_isSome_iff :
    checked.counterexample?.isSome = true ↔ checked.overCaptures.verdict = some false :=
  left.refinementCounterexample?_isSome_iff right

omit [DecidableEq F] in
/-- The original named witness supplies two successful decodes. Its exact
trace is present on the left, absent on the right, and refutes the sentence
in the all-replies model. -/
theorem refutes {witness : CaptureTraceWitness V signature} (original : witness.Refutes left right) :
    ∃ (a : Denote inputType) (b : Denote rightType),
      left.seed? witness.initial = some a ∧ right.seed? witness.initial = some b ∧
      HandledTrace signature.traceModel.step () (left.observeOccurrences a) witness.trace ∧
      ¬ HandledTrace signature.traceModel.step () (right.observeOccurrences b) witness.trace ∧
      ¬ TraceInstitution.Sat signature.traceModel (checked.sentence a b) :=
  witness.refutes_occurrences checked.leftAdmission checked.rightAdmission original

end OccurrenceComparison
end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
