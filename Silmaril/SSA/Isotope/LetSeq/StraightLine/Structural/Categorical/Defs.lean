module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Defs

/-! # Categorical models of the structural LetSeq equations -/

@[expose] public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical

open CategoryTheory
open LocallyNameless (Derivation)
open LetIter.Semantics.Categorical (ofTypeModel ofInstructionModel)
open scoped Structural

variable {α Φ : Type}

section Native

variable [Signature α Φ]

/-- The actual native typed inclusion into the existing categorical interpreter. -/
def asIter {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) :=
  Morphism.CaseIter.derivation (Morphism.SeqCase.derivation d)

/-- Use the repository's coherent, central-unit, shared-tensor class with
small homs. Validity compares arrows of the included native terms. -/
abbrev Valid {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) : Prop :=
  LetIter.Semantics.Categorical.Syntactic.RepairedLocallySmallValidity false (asIter d) (asIter e)

end Native

variable [HasTy Φ (Ty α)] in
abbrev traceJ := Kleisli.Adjunction.toKleisli (ofTypeMonad (Trace α Φ))

noncomputable abbrev traceTypes (α : Type) := ofTypeModel (Value (α := α))

variable [HasTy Φ (Ty α)] in
abbrev traceInstructions := ofInstructionModel (Value (α := α)) (model (Φ := Φ))

variable [Signature α Φ] in
/-- The categorical arrow in the actual ordered trace Kleisli category. -/
noncomputable def traceArrow {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) :=
  LetIter.Semantics.Categorical.denoteOfType Value (model (Φ := Φ)) (asIter d)

end Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical
