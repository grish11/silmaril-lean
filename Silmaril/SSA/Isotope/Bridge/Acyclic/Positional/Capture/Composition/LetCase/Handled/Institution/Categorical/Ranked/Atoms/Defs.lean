module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.TypeChange.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Coherence.Thms
public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Thms

/-! # Atom-bearing signatures in the categorical ranked room

Three properties of a ranked sentence are kept apart. Completeness says
that validity in the supported models gives native equality of the emitted
operands. A translation along a signature map reflects native equality
when native equality of the translated emitted operands gives native
equality of the original ones. It reflects validity when validity of the
translated sentence gives validity of the original one. Soundness and the
forward transports are theorems and are not part of these definitions.

The ordered trace interpretation of a signature typed over atoms gives
every atom the carrier `Nat`. A pair of ranked entries is reflected by
that interpretation when equal ordered trace arrows of the emitted
operands give native equality. The straight-line class below is over the
existing structural signatures whose primitive argument and reply types
are built from atoms, unit and ordered products.

An operand is straight-line when it is natively equal to a term of the
straight-line calculus returned at the single exit. The bound context is
one packed product slot.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation grammarCase readGrammar mapRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀ traceArrow)
open LetSeq.StraightLine.Structural (Shape Packed)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped LetSeq.StraightLine.Structural

/-! ## Completeness and the two reflections along a translation -/

section Translation

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ] {P : InstrSig τ ε} {Q : InstrSig υ δ}

/-- Validity of a ranked sentence in the supported models gives native
equality of its emitted operands. -/
def Complete (pe : ε) (e : RankedEquation P) : Prop :=
  RankedValid pe e → Derivable pe (grammarCase (readGrammar e))

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums] (pe : ε)

/-- The translation reflects native equality of the emitted operands of
this sentence. This is a property of syntax. -/
def ReflectsDerivable (e : RankedEquation P) : Prop :=
  Derivable (g.eff pe) (grammarCase (readGrammar (mapRanked g e))) → Derivable pe (grammarCase (readGrammar e))

/-- The translation reflects validity of this sentence in the supported
models. This is a property of models. -/
def ReflectsValid (e : RankedEquation P) : Prop :=
  RankedValid (g.eff pe) (mapRanked g e) → RankedValid pe e

end Translation

/-! ## Signatures with atoms -/

section Typed

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- A signature typed over atoms as an instruction signature of the
existing equational institutions. Every primitive is effectful. The
primitive types may use every type former. -/
abbrev atomSig (α Φ : Type) [HasTy Φ (Ty α)] : InstrSig (Ty α) Bool := ⟨Φ⟩

/-- The ordered trace interpretation whose atoms are natural numbers, as a
coherent region model of the existing rooms. -/
noncomputable def atomTraceModel (α Φ : Type) [HasTy Φ (Ty α)] :
    CoherentRegionModel (traceJ (α := α) (Φ := Φ)) (atomSig α Φ) :=
  ⟨traceTypes α, traceInstructions, atomTrace_region_coherent⟩

/-- The same interpretation as a model of the existing ranked room. -/
noncomputable def atomTraceRanked (α Φ : Type) [HasTy Φ (Ty α)] :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Mod :=
  ShrinkHoms.toShrinkHoms (Discrete.mk (atomTraceModel α Φ))

variable {d : Nat} {β : BoundCtx (Ty α) d} {L : List (Ty α)}

/-- The ranked sentence between two entries at one interface. -/
def sentenceOf (l r : RankedEntry Φ β L) : RankedEquation (atomSig α Φ) := ⟨⟨d, β, L⟩, l, r⟩

/-- The first row of a written checked graph as a ranked entry. -/
def entryOf (c : CheckedTable Φ β L) : RankedEntry Φ β L := ⟨c.size, c.table, c.checked, 0, c.entry⟩

/-- Equal ordered trace arrows of the two emitted operands give native
equality. The arrows are taken in the interpretation whose atoms are
natural numbers. -/
def TraceReflects (l r : RankedEntry Φ β L) : Prop :=
  traceArrow (emitted (P := atomSig α Φ) l).2 = traceArrow (emitted (P := atomSig α Φ) r).2 →
    Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1 (packedExitType L)

end Typed

variable {α Φ : Type} [LetSeq.StraightLine.Structural.Signature α Φ] {s : Shape α} {A : Ty α}

/-- A term of the straight-line calculus returned at the single exit, as
a captured LetCase operand over one packed product slot. -/
def lineOperand {t : LetSeq.LocallyNameless.Tm Empty Φ 1}
    (line : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A) :
    Operand Φ (Packed s) (packedExitType [A]) :=
  ⟨.inl (Morphism.SeqCase.embed t), .inl (Morphism.SeqCase.derivation line)⟩

/-- The operand is natively equal to a straight-line term returned at
the single exit. -/
def StraightLine (a : Operand Φ (Packed s) (packedExitType [A])) : Prop :=
  ∃ (t : LetSeq.LocallyNameless.Tm Empty Φ 1)
    (line : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A),
    Equiv false Γ₀ (Packed s) a.1 (lineOperand line).1 (packedExitType [A])

/-- The checked graph that the readback builds from a straight-line term. -/
def lineGraph {t : LetSeq.LocallyNameless.Tm Empty Φ 1}
    (line : LetSeq.LocallyNameless.Derivation Φ LetSeq.StraightLine.Structural.Γ₀ (Packed s) t A) :
    CheckedTable Φ (Packed s) [A] :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) (lineOperand line).2

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
