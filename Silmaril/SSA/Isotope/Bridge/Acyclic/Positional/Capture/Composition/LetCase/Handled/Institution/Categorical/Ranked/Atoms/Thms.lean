module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Defs
public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomTrace

/-! # Completeness for atom-bearing signatures in the categorical ranked room

The existing completeness theorem of the ranked room is for signatures
whose types have no atoms. This file has two results beyond it.

The first is a criterion for translations. Native equality and validity
both move forward along every signature map. A translation into a
complete target reflects native equality of a sentence exactly when it
reflects validity of that sentence and the source is complete for it. Under
that reflection, validity is decided by the pullback of the target's
ordered trace model. Reflection is a hypothesis here. It is not a
consequence of forward transport. The regression has a translation,
sending an atom to the unit type, that fails it on a sentence between two
captured atoms.

The second is a completeness theorem that uses no translation. For every
signature typed over atoms, the ordered trace interpretation whose atoms
are natural numbers is a supported model of the ranked room. Over the
structural signatures built from atoms, unit and ordered products it
reflects native equality of operands that are natively equal to
straight-line terms returned at the single exit, over one packed product
slot. A ranked sentence between such entries is valid in all supported
models exactly when its emitted operands are natively equal.

Operands with a case on a reply, more than one exit, or an older context
beside the packed slot are outside the second result. Reflection by the
same interpretation is stated in general as the hypothesis
`TraceReflects`. It is proved for one branching class in `Branching`.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation mapCaseSignature regionWitnessPullback)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation grammarCase readGrammar mapRanked
  readGrammar_map grammarCase_map)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀ traceArrow traceArrow_of_valid valid_of_equiv)
open LetSeq.StraightLine.Structural (Shape Packed)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## Forward transport along a translation -/

section Translation

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ] {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums] (pe : ε)

/-- Native equality of a LetCase sentence is preserved by every signature
map, from a source marker to its image. -/
theorem derivable_mapCase (c : CaseEquation P) (h : Derivable pe c) :
    Derivable (g.eff pe) (mapCaseSignature g c) :=
  derivable_mapCase_proof g pe c h

/-- Native equality of the emitted operands of a ranked sentence is
preserved by every signature map. The translated sentence is the one
built by the existing ranked signature map. -/
theorem derivable_mapRanked (e : RankedEquation P) (h : Derivable pe (grammarCase (readGrammar e))) :
    Derivable (g.eff pe) (grammarCase (readGrammar (mapRanked g e))) := by
  rw [readGrammar_map, grammarCase_map]
  exact derivable_mapCase g pe _ h

/-! ## The reflection criterion -/

/-- A translation that reflects validity, from a source that is complete,
reflects native equality. The target needs no completeness. -/
theorem reflectsDerivable_of_reflectsValid (e : RankedEquation P) (valid : ReflectsValid g pe e)
    (complete : Complete pe e) : ReflectsDerivable g pe e :=
  fun h => complete (valid (rankedValid_of_derivable _ h))

/-- A translation into a complete target that reflects native equality
reflects validity. -/
theorem reflectsValid_of_reflectsDerivable (e : RankedEquation P)
    (target : Complete (g.eff pe) (mapRanked g e)) (reflects : ReflectsDerivable g pe e) :
    ReflectsValid g pe e :=
  fun valid => rankedValid_of_derivable e (reflects (target valid))

/-- A translation into a complete target that reflects native equality
makes the source complete. Validity moves forward by the closure of the
supported models under pullback. -/
theorem complete_of_reflectsDerivable (e : RankedEquation P)
    (target : Complete (g.eff pe) (mapRanked g e)) (reflects : ReflectsDerivable g pe e) :
    Complete pe e :=
  fun valid => reflects (target (rankedValid_mapRanked_typeChange g e valid))

/-- Into a complete target, reflection of native equality is reflection of
validity together with completeness of the source. -/
theorem reflectsDerivable_iff (e : RankedEquation P) (target : Complete (g.eff pe) (mapRanked g e)) :
    ReflectsDerivable g pe e ↔ ReflectsValid g pe e ∧ Complete pe e :=
  ⟨fun reflects => ⟨reflectsValid_of_reflectsDerivable g pe e target reflects,
      complete_of_reflectsDerivable g pe e target reflects⟩,
    fun both => reflectsDerivable_of_reflectsValid g pe e both.1 both.2⟩

/-- Under reflection of native equality into a complete target, a ranked
sentence is valid exactly when its emitted operands are natively equal. -/
theorem rankedValid_iff_of_reflectsDerivable (e : RankedEquation P)
    (target : Complete (g.eff pe) (mapRanked g e)) (reflects : ReflectsDerivable g pe e) :
    RankedValid pe e ↔ Derivable pe (grammarCase (readGrammar e)) :=
  ⟨complete_of_reflectsDerivable g pe e target reflects, rankedValid_of_derivable e⟩

/-- Under the same hypotheses, a sentence and its translation are valid
together. -/
theorem rankedValid_iff_translated (e : RankedEquation P)
    (target : Complete (g.eff pe) (mapRanked g e)) (reflects : ReflectsDerivable g pe e) :
    RankedValid pe e ↔ RankedValid (g.eff pe) (mapRanked g e) :=
  ⟨rankedValid_mapRanked_typeChange g e, reflectsValid_of_reflectsDerivable g pe e target reflects⟩

end Translation

/-! ## Translations into the finite structural fragment -/

section Structural

variable {Ψ : Type} [LetCase.Structural.Finite.Signature Ψ]

/-- The finite structural fragment is complete over a separated bound
context. This is the existing completeness theorem. -/
theorem complete_structural (e : RankedEquation (sig Ψ))
    (separated : Separated (Φ := Ψ) (grammarCase (readGrammar e)).1.bound) : Complete false e :=
  (rankedValid_iff e separated).mp

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  (g : SignatureMap P.Instr (sig Ψ).Instr τ (Ty Empty) ε Bool) [g.PreservesProducts] [g.PreservesSums]
  {pe : ε}

/-- Under reflection of native equality into the finite structural
fragment, validity is decided by one model: the pullback of the ordered
trace model along the translation. The translated bound context is
separated and the source marker is sent to the target marker. -/
theorem rankedValid_iff_pulledTrace (marker : g.eff pe = false) (e : RankedEquation P)
    (separated : Separated (Φ := Ψ) (grammarCase (readGrammar (mapRanked g e))).1.bound)
    (reflects : ReflectsDerivable g pe e) :
    RankedValid pe e ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Ψ)) P).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk ((traceRegionModel Ψ).pullbackOfWitness g
          (regionWitnessPullback g (traceRegionModel Ψ))))) e :=
  ⟨fun valid => valid (traceJ (α := Empty) (Φ := Ψ)) _
      (supported_pullback g (traceRegionModel Ψ) (regionWitnessPullback g (traceRegionModel Ψ))
        (by rw [marker]; exact trace_supported)),
    fun holds => rankedValid_of_derivable e (reflects (by
      rw [marker]
      exact derivable_of_trace (mapRanked g e) separated ((sat_pullback g (traceRegionModel Ψ) e).mpr holds)))⟩

end Structural

/-! ## The ordered trace model with atoms -/

section Typed

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- The ordered trace model with atoms is a supported model of the ranked
room. -/
theorem atomTrace_supported : Supported false (atomTraceModel α Φ) :=
  atomTrace_supported_proof

/-- Satisfaction at the ordered trace model with atoms is equality of the
ordered trace arrows of the two emitted operands. -/
theorem atomTrace_sat_iff (e : RankedEquation (atomSig α Φ)) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) e ↔
      traceArrow (emitted e.2.1).2 = traceArrow (emitted e.2.2).2 :=
  atomTrace_denoteRanked_iff_proof e.2.1 e.2.2

/-- A sentence that holds at the ordered trace model with atoms, between
entries that the model reflects, is natively derivable. -/
theorem derivable_of_atomTrace (e : RankedEquation (atomSig α Φ)) (reflects : TraceReflects e.2.1 e.2.2)
    (holds : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ))
      (atomSig α Φ)).Sat (atomTraceRanked α Φ) e) :
    Derivable false (grammarCase (readGrammar e)) :=
  (derivable_iff false e).mpr (reflects ((atomTrace_sat_iff e).mp holds))

/-- Completeness for the entries that the model reflects. -/
theorem complete_of_traceReflects (e : RankedEquation (atomSig α Φ)) (reflects : TraceReflects e.2.1 e.2.2) :
    Complete false e :=
  fun valid => derivable_of_atomTrace e reflects (valid (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ)
    atomTrace_supported)

/-- Soundness and completeness for the entries that the model reflects. -/
theorem rankedValid_iff_of_traceReflects (e : RankedEquation (atomSig α Φ))
    (reflects : TraceReflects e.2.1 e.2.2) :
    RankedValid false e ↔ Derivable false (grammarCase (readGrammar e)) :=
  ⟨complete_of_traceReflects e reflects, rankedValid_of_derivable e⟩

/-- For those entries, validity is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_iff_atomTrace (e : RankedEquation (atomSig α Φ)) (reflects : TraceReflects e.2.1 e.2.2) :
    RankedValid false e ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) e :=
  ⟨fun valid => valid (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) atomTrace_supported,
    fun holds => rankedValid_of_derivable e (derivable_of_atomTrace e reflects holds)⟩

end Typed

/-! ## Straight-line operands -/

variable {α Φ : Type} [LetSeq.StraightLine.Structural.Signature α Φ]
  {s : Shape α} {A : Ty α} {t u : LetSeq.LocallyNameless.Tm Empty Φ 1}

/-- Two straight-line terms returned at the single exit are natively
equal as captured LetCase operands exactly when they are natively equal in
the straight-line calculus. -/
theorem lineOperand_equiv_iff
    (dt : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A)
    (du : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) u A) :
    Equiv false Γ₀ (Packed s) (lineOperand dt).1 (lineOperand du).1 (packedExitType [A]) ↔
      LetSeq.LocallyNameless.Equiv false LetSeq.StraightLine.Structural.Γ₀ (Packed s) t u A :=
  ⟨fun h => line_reflects_proof dt du
      (traceArrow_of_valid (valid_of_equiv (lineOperand dt).2 (lineOperand du).2 h)),
    lineOperand_congr_proof dt du⟩

/-- An operand natively equal to a straight-line operand is straight-line. -/
theorem StraightLine.congr {a b : Operand Φ (Packed s) (packedExitType [A])}
    (h : Equiv false Γ₀ (Packed s) a.1 b.1 (packedExitType [A])) (line : StraightLine b) : StraightLine a :=
  let ⟨t, dt, same⟩ := line
  ⟨t, dt, h.trans same⟩

/-- The graph read back from a straight-line term emits a straight-line
operand. -/
theorem straightLine_lineGraph
    (dt : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A) :
    StraightLine (lineGraph dt).toLetCase :=
  ⟨t, dt, CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand dt).2⟩

/-- The ordered trace interpretation with atoms reflects native equality
of straight-line operands. -/
theorem straightLine_reflects (a b : Operand Φ (Packed s) (packedExitType [A]))
    (ha : StraightLine a) (hb : StraightLine b) (same : traceArrow a.2 = traceArrow b.2) :
    Equiv false Γ₀ (Packed s) a.1 b.1 (packedExitType [A]) :=
  straightLine_reflects_proof a b ha hb same

/-- Entries with straight-line emitted operands are reflected. -/
theorem straightLine_traceReflects (l r : RankedEntry Φ (Packed s) [A])
    (hl : StraightLine (emitted (P := atomSig α Φ) l)) (hr : StraightLine (emitted (P := atomSig α Φ) r)) :
    TraceReflects l r :=
  straightLine_reflects _ _ hl hr

/-! ## Soundness and completeness with atoms -/

/-- A ranked sentence between entries with straight-line emitted operands
holds in every supported model of the ranked room exactly when the emitted
operands are natively equal. -/
theorem rankedValid_straightLine_iff (l r : RankedEntry Φ (Packed s) [A])
    (hl : StraightLine (emitted (P := atomSig α Φ) l)) (hr : StraightLine (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      Equiv false Γ₀ (Packed s) (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1
        (packedExitType [A]) :=
  (rankedValid_iff_of_traceReflects (sentenceOf l r) (straightLine_traceReflects l r hl hr)).trans
    (derivable_iff false (sentenceOf l r))

/-- Validity of such a sentence is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_straightLine_iff_atomTrace (l r : RankedEntry Φ (Packed s) [A])
    (hl : StraightLine (emitted (P := atomSig α Φ) l)) (hr : StraightLine (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) (sentenceOf l r) :=
  rankedValid_iff_atomTrace (sentenceOf l r) (straightLine_traceReflects l r hl hr)

/-- On the graphs read back from two straight-line terms, validity in the
ranked room is native equality in the straight-line calculus. -/
theorem rankedValid_line_iff
    (dt : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A)
    (du : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) u A) :
    RankedValid false (sentenceOf (entryOf (lineGraph dt)) (entryOf (lineGraph du))) ↔
      LetSeq.LocallyNameless.Equiv false LetSeq.StraightLine.Structural.Γ₀ (Packed s) t u A :=
  (rankedValid_straightLine_iff (entryOf (lineGraph dt)) (entryOf (lineGraph du))
    (straightLine_lineGraph dt) (straightLine_lineGraph du)).trans
    ⟨fun h => (lineOperand_equiv_iff dt du).mp
        (((CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand dt).2).symm.trans h).trans
          (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand du).2)),
      fun h => ((CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand dt).2).trans
        ((lineOperand_equiv_iff dt du).mpr h)).trans
          (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) (lineOperand du).2).symm⟩

/-! ## Translations of straight-line sentences -/

/-- For a sentence between straight-line entries, a translation into the
finite structural fragment reflects native equality exactly when it
reflects validity. The source is complete by the ordered trace model with
atoms and the target by the existing theorem. Whether a given translation
reflects validity is a separate question. -/
theorem straightLine_reflectsDerivable_iff {Ψ : Type} [LetCase.Structural.Finite.Signature Ψ]
    (g : SignatureMap (atomSig α Φ).Instr (sig Ψ).Instr (Ty α) (Ty Empty) Bool Bool)
    [g.PreservesProducts] [g.PreservesSums] (marker : g.eff false = false)
    (l r : RankedEntry Φ (Packed s) [A])
    (hl : StraightLine (emitted (P := atomSig α Φ) l)) (hr : StraightLine (emitted (P := atomSig α Φ) r))
    (separated : Separated (Φ := Ψ) (grammarCase (readGrammar (mapRanked g (sentenceOf l r)))).1.bound) :
    ReflectsDerivable g false (sentenceOf l r) ↔ ReflectsValid g false (sentenceOf l r) :=
  (reflectsDerivable_iff g false (sentenceOf l r)
    (by rw [marker]; exact complete_structural _ separated)).trans
    (and_iff_left (complete_of_traceReflects (sentenceOf l r) (straightLine_traceReflects l r hl hr)))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
