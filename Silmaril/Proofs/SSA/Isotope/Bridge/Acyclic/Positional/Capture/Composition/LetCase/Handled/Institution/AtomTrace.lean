module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Defs
public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Thms
import Silmaril.Semantics.NondeterministicTrace.Finite.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation mapCaseSignature)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry denoteRanked)
open Region (packedExitType)
open LetIter.Semantics.Categorical (typingCoherent_ofType)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀ traceArrow traceArrow_of_valid valid_of_equiv traceArrow_eq_iff_run)
open LetSeq.StraightLine.Structural (Shape Packed packedEnv model packed_run_eq_iff_native)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open Silmaril.Semantics.NondeterministicTrace (Finite)
open scoped LetSeq.StraightLine.Structural

/-! ## Forward transport of native equality -/

section Translation

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ] {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums] (pe : ε)

/-- Native equality of a LetCase sentence is preserved by every signature
map, from a source marker to its image. -/
theorem derivable_mapCase_proof (c : CaseEquation P) (h : Derivable pe c) :
    Derivable (g.eff pe) (mapCaseSignature g c) :=
  LetCase.LocallyNameless.Equiv.mapInstr g h

end Translation

/-! ## The ordered trace model with atoms -/

set_option backward.isDefEq.respectTransparency false

section Typed

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- The ordered trace model with atoms is a supported model. -/
theorem atomTrace_supported_proof : Supported false (atomTraceModel α Φ) := by
  classical
  exact ⟨typingCoherent_ofType (ν := Empty) (fun _ : α => Nat) model,
    fun _ _ => ⟨rfl, rfl⟩, fun _ pure => by cases pure⟩

/-- At the ordered trace model with atoms, two entries have the same
ordered-exit arrow exactly when their emitted operands have the same
ordered trace arrow. -/
theorem atomTrace_denoteRanked_iff_proof {d : Nat} {β : BoundCtx (Ty α) d} {L : List (Ty α)}
    (l r : RankedEntry Φ β L) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) l =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) r ↔
      traceArrow (emitted (P := atomSig α Φ) l).2 = traceArrow (emitted (P := atomSig α Φ) r).2 := by
  refine (denoteRanked_eq_iff (atomTraceModel α Φ) l r).trans ?_
  let := traceInstructions (α := α) (Φ := Φ)
  unfold traceArrow LetIter.Semantics.Categorical.denoteOfType
  rw [Native.denote_caseIter (traceJ (α := α) (Φ := Φ)) (traceTypes α),
    Native.denote_caseIter (traceJ (α := α) (Φ := Φ)) (traceTypes α)]
  exact Iff.rfl

end Typed

/-! ## Straight-line operands -/

variable {α Φ : Type} [LetSeq.StraightLine.Structural.Signature α Φ]
  {s : Shape α} {A : Ty α} {t u : LetSeq.LocallyNameless.Tm Empty Φ 1}

/-- Two straight-line terms returned at the single exit with equal
ordered trace arrows are natively equal in the straight-line calculus. The
one separating input gives distinct tokens to the atom leaves. -/
theorem line_reflects_proof
    (dt : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A)
    (du : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) u A)
    (same : traceArrow (lineOperand dt).2 = traceArrow (lineOperand du).2) :
    LetSeq.LocallyNameless.Equiv false LetSeq.StraightLine.Structural.Γ₀ (Packed s) t u A := by
  classical
  have runs := (traceArrow_eq_iff_run (lineOperand dt).2 (lineOperand du).2).mp same (packedEnv s (s.fresh 0))
  refine (packed_run_eq_iff_native dt du).mp ?_
  apply Finite.outcomes_injective
  apply Set.image_injective.mpr (Sum.inl_injective.prodMap Function.injective_id)
  rw [← Finite.outcomes_bind_pure, ← Finite.outcomes_bind_pure]
  have out := congrArg Finite.outcomes runs
  simp only [LetCase.Structural.Reply.run, lineOperand, LetCase.LocallyNameless.Derivation.denote,
    Morphism.SeqCase.denote_derivation] at out
  exact out

/-- Straight-line terms that are natively equal in the straight-line
calculus give natively equal operands. -/
theorem lineOperand_congr_proof
    (dt : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A)
    (du : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) u A)
    (h : LetSeq.LocallyNameless.Equiv false LetSeq.StraightLine.Structural.Γ₀ (Packed s) t u A) :
    Equiv false Γ₀ (Packed s) (lineOperand dt).1 (lineOperand du).1 (packedExitType [A]) :=
  Equiv.inl (Morphism.SeqCase.embed_equiv h)

/-- The ordered trace interpretation with atoms reflects native equality
of straight-line operands. -/
theorem straightLine_reflects_proof (a b : Operand Φ (Packed s) (packedExitType [A]))
    (ha : StraightLine a) (hb : StraightLine b) (same : traceArrow a.2 = traceArrow b.2) :
    Equiv false Γ₀ (Packed s) a.1 b.1 (packedExitType [A]) := by
  obtain ⟨t, dt, et⟩ := ha
  obtain ⟨u, du, eu⟩ := hb
  have left : traceArrow a.2 = traceArrow (lineOperand dt).2 :=
    traceArrow_of_valid (valid_of_equiv a.2 (lineOperand dt).2 et)
  have right : traceArrow b.2 = traceArrow (lineOperand du).2 :=
    traceArrow_of_valid (valid_of_equiv b.2 (lineOperand du).2 eu)
  exact (et.trans (lineOperand_congr_proof dt du
    (line_reflects_proof dt du (left.symm.trans (same.trans right))))).trans eu.symm

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
