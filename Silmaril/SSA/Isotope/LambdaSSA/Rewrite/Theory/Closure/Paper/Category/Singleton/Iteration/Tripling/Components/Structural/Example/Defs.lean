module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Defs

/-! # A written round on a product of two Bits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.StructuralExample

inductive Op
  | sample

abbrev U : Ty Empty := .unit
abbrev Bit : Ty Empty := .coprod U U
abbrev Exit : Ty Empty := .coprod U (.product U U)
abbrev bit : StructuralState := .sum .unit .unit
abbrev shape : StructuralState := .product bit bit
abbrev State : Ty Empty := shape.ty
abbrev Reply : Ty Empty := .coprod State Exit

instance : HasTy Op (Ty Empty) where
  src _ := State
  trg _ := Reply

instance : HasEff Op Bool := ⟨fun _ => true⟩

/-- The primitive observes both retained factors. Its reply supplies the next
pair or chooses one of the two ordered exits. -/
def body : Region Op :=
  .let₁ (.op .sample (.var 0))
    (.case (.var 0) (.br 0 (.inr (.var 0))) (.br 0 (.inl (.var 0))))

def unpack : Region Op :=
  .case (.var 0) (.case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))) (.br 2 (.var 0))

def orderedBody : Region Op := body.lsubst (fun _ => unpack)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.StructuralExample
