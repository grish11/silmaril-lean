module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Refinement.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Refinement

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  {left : StructuralEntry signature source exits fields inputType outputs}
  {right : StructuralEntry signature target exits fields rightType outputs}
  (leftAdmission : OccurrenceAdmission left) (rightAdmission : OccurrenceAdmission right)

theorem sentence_eq
    (initial : V → Value Atom) (a : Denote inputType) (b : Denote rightType)
    (ha : left.seed? initial = some a) (hb : right.seed? initial = some b) :
    leftAdmission.refinementSentence rightAdmission a b = left.versionedRefinementSentence right initial := by
  unfold OccurrenceAdmission.refinementSentence StructuralEntry.versionedRefinementSentence
  erw [left.observeVersioned_eq_occurrences initial a ha, right.observeVersioned_eq_occurrences initial b hb]

theorem store_iff [DecidableEq F]
    (initial : V → Value Atom) (verdict : Bool) :
    left.refinementFromStore? right initial = some verdict ↔
      ∃ (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a ∧ right.seed? initial = some b ∧
        (verdict = true ↔ ∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (leftAdmission.refinementSentence rightAdmission a b)) := by
  rw [left.refinementFromStore?_eq_some_iff right initial verdict]
  have compare (a : Denote inputType) (b : Denote rightType)
      (ha : left.seed? initial = some a) (hb : right.seed? initial = some b) :
      (∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (observeRaw signature.primitive exits fields source initial) trace →
          HandledTrace policy.step x (observeRaw signature.primitive exits fields target initial) trace) ↔
      (∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
        TraceInstitution.Sat policy (leftAdmission.refinementSentence rightAdmission a b)) := by
    rw [sentence_eq leftAdmission rightAdmission initial a b ha hb, left.versionedRefinementSentence_eq right initial]
    constructor
    · intro incl policy x hx trace seen
      exact (incl policy x hx trace seen).1
    · intro sat policy x hx trace seen
      exact ⟨sat policy x hx trace seen, seen.2⟩
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩
    have sa : left.seed? initial = some a := (decodeSeed?_eq_some_iff _ _ _).mpr ha
    have sb : right.seed? initial = some b := (decodeSeed?_eq_some_iff _ _ _).mpr hb
    exact ⟨a, b, sa, sb, h.trans (compare a b sa sb)⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨⟨a, (decodeSeed?_eq_some_iff _ _ _).mp ha⟩, ⟨b, (decodeSeed?_eq_some_iff _ _ _).mp hb⟩,
      h.trans (compare a b ha hb).symm⟩

theorem domain_iff [DecidableEq F] :
    (left.refinementOverCaptures right).verdict = some true ↔
      ∀ initial (a : Denote inputType) (b : Denote rightType),
        left.seed? initial = some a → right.seed? initial = some b →
        ∀ policy : Model.{0, 0} signature.traceSignature.toSignature,
          TraceInstitution.Sat policy (leftAdmission.refinementSentence rightAdmission a b) := by
  rw [left.refinementOverCaptures_iff_valid_versioned right]
  exact forall_congr' fun initial => forall_congr' fun a => forall_congr' fun b =>
    imp_congr_right fun ha => imp_congr_right fun hb => by rw [sentence_eq leftAdmission rightAdmission initial a b ha hb]

theorem witness_refutes
    {witness : CaptureTraceWitness V signature} (refutes : witness.Refutes left right) :
    ∃ (a : Denote inputType) (b : Denote rightType),
      left.seed? witness.initial = some a ∧ right.seed? witness.initial = some b ∧
      HandledTrace signature.traceModel.step () (left.observeOccurrences a) witness.trace ∧
      ¬ HandledTrace signature.traceModel.step () (right.observeOccurrences b) witness.trace ∧
      ¬ TraceInstitution.Sat signature.traceModel (leftAdmission.refinementSentence rightAdmission a b) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := left.jointStores_typed right refutes.1
  have sa : left.seed? witness.initial = some a := (decodeSeed?_eq_some_iff _ _ _).mpr ha
  have sb : right.seed? witness.initial = some b := (decodeSeed?_eq_some_iff _ _ _).mpr hb
  have separated := witness.refutes_versioned left right refutes
  refine ⟨a, b, sa, sb, ?_⟩
  erw [← left.observeVersioned_eq_occurrences witness.initial a sa,
    ← right.observeVersioned_eq_occurrences witness.initial b sb, sentence_eq leftAdmission rightAdmission witness.initial a b sa sb]
  exact separated

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Refinement
