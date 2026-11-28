module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Defs

/-! # A written three-tag loop with two ordered exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.UnitTree.Example

inductive Op
  | first | second

abbrev U : Ty Empty := .unit
abbrev Reply : Ty Empty := .coprod U U
abbrev Exit : Ty Empty := .coprod U (.product U U)
abbrev shape : UnitTree := .sum .unit (.sum .unit .unit)
abbrev State : Ty Empty := shape.ty

instance : HasTy Op (Ty Empty) where
  src _ := U
  trg _ := Reply

instance : HasEff Op Bool := ⟨fun _ => true⟩

/-- The first request either advances to the middle tag or exits at the
Unit port. The second request either advances to the last tag or exits at
the product port. The last tag returns to the first. -/
def body : Region Op :=
  .case (.var 0)
    (.let₁ (.op .first (.var 0))
      (.case (.var 0)
        (.br 0 (.inr (.inr (.inl (.var 0)))))
        (.br 0 (.inl (.inl .unit)))))
    (.case (.var 0)
      (.let₁ (.op .second (.var 0))
        (.case (.var 0)
          (.br 0 (.inr (.inr (.inr (.var 0)))))
          (.br 0 (.inl (.inr (.pair .unit .unit))))))
      (.br 0 (.inr (.inl (.var 0)))))

/-- Expose the two outward ports in order, followed by the recurrence port. -/
def unpack : Region Op :=
  .case (.var 0) (.case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))) (.br 2 (.var 0))

def orderedBody : Region Op := body.lsubst (fun _ => unpack)


end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.UnitTree.Example
