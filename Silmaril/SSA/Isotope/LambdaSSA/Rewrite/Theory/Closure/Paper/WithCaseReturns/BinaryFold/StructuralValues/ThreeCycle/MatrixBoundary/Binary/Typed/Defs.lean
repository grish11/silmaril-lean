module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs

/-! # A typed BinaryFold instance with an effectful Bit request -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary.Binary

open CategoryTheory CategoryTheory.Limits
open Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary (PhaseState)

abbrev ExitTy : Ty Empty := .unit
abbrev BitTy : Ty Empty := .coprod ExitTy ExitTy
abbrev PhaseTy : Ty Empty := .coprod BitTy BitTy

inductive Op
  | poll

instance : HasTy Op (Ty Empty) where
  src _ := BitTy
  trg _ := .coprod ExitTy BitTy

instance : HasEff Op Bool := ⟨fun _ => true⟩

abbrev Native (A : Ty Empty) := Paper.TypeCategory.ofType (Φ := Op) A

/-- Left replies exit and right replies carry an arbitrary next Bit. -/
noncomputable def round : Native BitTy ⟶ Native ExitTy ⨿ Native BitTy :=
  Paper.TypeCategory.primitiveReturn Op.poll ≫ (Paper.TypeCategory.sumIso ExitTy BitTy).hom

/-- The scalar carrier coordinates distinguish the two constructor Bits. -/
def bitValue (i : Fin 2) : Tm Op := if i = 0 then .inl .unit else .inr .unit

def phaseValue : PhaseState → Tm Op
  | .inl i => .inl (bitValue i)
  | .inr i => .inr (bitValue i)

/-- Select the actual initial phase and Bit with a closed constructor. -/
def entry (initial : PhaseState) : Region Op := .br 0 (phaseValue initial)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.MatrixBoundary.Binary
