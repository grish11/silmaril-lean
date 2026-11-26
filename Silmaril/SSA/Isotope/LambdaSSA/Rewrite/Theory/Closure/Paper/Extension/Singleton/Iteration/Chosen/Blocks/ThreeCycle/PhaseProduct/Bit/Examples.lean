module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.PhaseProduct.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs

/-! # A Bit-state poll whose recurrence factors through Unit -/

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.PhaseProductExample

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

private inductive Op
  | poll
  | restore

local notation "U" => (Ty.unit : Ty Empty)
local notation "Bit" => Ty.coprod U U

local instance : HasTy Op (Ty Empty) where
  src
    | .poll => Bit
    | .restore => U
  trg _ := Bit

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private abbrev Seed := Paper.WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) false
local notation "Obj" => ofType Seed

/-- A primitive can inspect the Bit on entry. On recurrence, the selected
reply goes through Unit before a second primitive supplies the next Bit. -/
example :
    let first : Obj Bit ⟶ Obj U ⨿ Obj U :=
      (projection Seed).map (Paper.TypeCategory.primitiveReturn Op.poll) ≫ (sumIso Seed U U).hom
    let restore : Obj U ⟶ Obj Bit :=
      (projection Seed).map (Paper.TypeCategory.primitiveReturn Op.restore)
    let g := first ≫ coprod.map (𝟙 (Obj U)) restore
    iterateChosen Seed (triple g) = iterateChosen Seed g :=
  triple_step_through_unit Seed (fun h => .inl (Paper.WithCaseReturns.includeUnit false h))
    _ ((projection Seed).map (Paper.TypeCategory.primitiveReturn Op.restore))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.PhaseProductExample
