module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.Reification

/-! # Packed native LetIter reification in the abort-extended presentation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (packedArrow)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local instance reificationThesisTypeFormers : Thesis.LambdaIter.TypeFormers τ :=
  Bridge.thesisTypeFormers τ
local instance reificationThesisHasTy : Thesis.LambdaIter.HasTy Φ τ :=
  Bridge.thesisHasTy Φ τ

/-- A native derivation reifies to its packed syntax representative in the abort-extended
presentation. The bound context is arbitrary and the free context is empty. -/
theorem packedNative_repaired_reification (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr .nil
      (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A) :
    repairedHomClass pe (packedNative pe d) =
      repairedHomClass pe (packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :=
  ReificationProofs.packedNative_repaired_reification pe d h

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
