module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms

/-! A two-block graph uses both primitive symbols and distinct packet
registers. Global versioning inserts a carry at its otherwise wire-only entry. -/

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

private def graph : Graph Nat Bool 1 1 where
  locals := 2
  entry _ := .inl 0
  block index :=
    if index = 0 then
      ⟨1, .let1 3 (.app true (.var 1)) (.term (.br (.inl 1) (.var 3)))⟩
    else
      ⟨2, .let1 4 (.app false (.var 2)) (.term (.br (.inr 0) (.var 4)))⟩
  closed index := by
    by_cases first : index = 0 <;>
      simp [first, Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def forgetPrimitive : Bool → Unit := fun _ => ()

-- This non-injective action preserves literal linked syntax.
example : (graph.link graph).mapOp forgetPrimitive =
    (graph.mapOp forgetPrimitive).link (graph.mapOp forgetPrimitive) :=
  Graph.mapOp_link forgetPrimitive graph graph

example : (graph.namedRTL 0).entry.toRegion.fv = {(0 : Nat)} := by decide

-- The global compiler wraps the input in a carry containing, among other
-- entries, the version-zero register for the *other* block's parameter.
example : (graph.namedSSA 0).graph.entry =
    .term (.br (.inl 0) (.pair (.var (0, 0)) (.pair (.var (0, 0)) (.pair (.var (2, 0)) .unit)))) := by
  decide

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
