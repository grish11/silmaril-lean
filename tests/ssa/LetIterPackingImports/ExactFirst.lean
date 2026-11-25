module

import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Thms

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation)
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
open Silmaril.Thesis.LambdaIter.Syn.SynCat (packedArrow)

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

example (pe : ε) :
    repairedHomClass pe
      (packedNative pe (Derivation.unit (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := .nil))) =
    repairedHomClass pe (packedArrow (S := signature (τ := τ) (Φ := Φ) pe) .unit) :=
  congrArg (repairedHomClass pe) (packedNative_unit_eq_packedArrow pe .unit)
