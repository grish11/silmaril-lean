module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs

/-! # A mixed, effectful Bit round -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.Example

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton.Generation (primitive)

inductive Op
  | poll

abbrev U : Ty Empty := .unit
abbrev Bit : Ty Empty := .coprod U U
abbrev Reply : Ty Empty := .coprod U Bit

instance : HasTy Op (Ty Empty) where
  src _ := Bit
  trg _ := Reply

instance : HasEff Op Bool := ⟨fun _ => true⟩

abbrev Seed := Paper.WithUnitEta.Step (τ := Ty Empty) (Φ := Op)
abbrev Obj := Paper.Extension.Singleton.ofType Seed

/-- The effect receives the current tag. Its reply can exit, stay, or cross
to the other tag for either input. -/
noncomputable def round : Obj Bit ⟶ Obj U ⨿ Obj Bit :=
  primitive Seed Op.poll ≫ (Paper.Extension.Singleton.sumIso Seed U Bit).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling.Example
