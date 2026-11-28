module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example.Defs

/-! # Two nested visible discriminators in a selected case tree -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Semantics.Categorical Semantics.Interaction.Typed
open Silmaril.Elgot.ITree
open SumCase.Example (Atom Payload Labels PayloadValue Model Op Request exit0 exit1)

attribute [local instance] typeModel

local notation "M" => ofMonadicTypeModel (τ := Ty Atom)

abbrev Carried := product Payload Payload

def inner : CaseTree Op Carried Labels :=
  .case Payload Payload (.call Op.choose (.snd Payload Payload))
    (.exit 1 rfl (.returned (.seq (.fst Carried Payload) (.fst Payload Payload))))
    (.exit 0 rfl (.returned (.snd Carried Payload)))

def nested : CaseTree Op Payload Labels :=
  .case Payload Payload (.call Op.choose .input) inner
    (.exit 1 rfl (.returned (.snd Payload Payload)))

noncomputable def expectedInner (x a : PayloadValue) : Model (labelObj M Labels) :=
  vis (Request.choose a.down) (fun
    | .inl _ => pure (exit1 x.down)
    | .inr b => pure (exit0 b))

noncomputable def expected (x : PayloadValue) : Model (labelObj M Labels) :=
  vis (Request.choose x.down) (fun
    | .inl a => expectedInner x (ULift.up a)
    | .inr b => pure (exit1 b))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Example
