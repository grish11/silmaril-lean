module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Thms
import Mathlib.Data.Nat.Pairing

/-! Both stages use private address zero. The left stage takes a back edge,
then forwards its decremented packet to the right stage. -/

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open Silmaril.Elgot

private def model : Model Unit Part Nat where
  unit := 0
  pair := Nat.pair
  inl := id
  inr := Nat.succ
  unpair n := pure (Nat.unpair n)
  split
    | 0 => pure (.inl 0)
    | n + 1 => pure (.inr n)
  app _ n := pure (n + 1)
  abort _ := Part.none

private def left : Graph Bool Unit 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨false, .term (.case (.val (.var false))
    false (.br (.inr 0) (.var false)) false (.br (.inl 0) (.var false)))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def right : Graph Bool Unit 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨false, .let1 true (.app () (.var false)) (.term (.br (.inr 0) (.var true)))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

example : ((left.link right).table.lookup (.inl (0 : Fin 3))).map (fun block => block.body.targets) =
    some [.inl (1 : Fin 3), .inl (0 : Fin 3)] := by decide

example : ((left.link right).table.lookup (.inl (1 : Fin 3))).map (fun block => block.body.targets) =
    some [.inl (2 : Fin 3)] := by decide

private theorem leftReturns : left.denote model (0, 1) = Part.some (0, 0) := by
  change iter (left.step model) (.inl (0 : Fin 1), 1) = Part.some (0, 0)
  apply Part.eq_some_iff.mpr
  apply (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
  have back : left.step model (.inl (0 : Fin 1), 1) = Part.some (.inr (.inl (0 : Fin 1), 0)) := by
    simp [Graph.step, left, model, Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, upd]
  have exit : left.step model (.inl (0 : Fin 1), 0) = Part.some (.inr (.inr 0, 0)) := by
    simp [Graph.step, left, model, Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, upd]
  exact .more (Part.eq_some_iff.mp back) <| .more (Part.eq_some_iff.mp exit) <|
    .done (Part.mem_some _)

private theorem rightReturns : right.denote model (0, 0) = Part.some (0, 1) := by
  change iter (right.step model) (.inl (0 : Fin 1), 0) = Part.some (0, 1)
  apply Part.eq_some_iff.mpr
  apply (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
  have exit : right.step model (.inl (0 : Fin 1), 0) = Part.some (.inr (.inr 0, 1)) := by
    simp [Graph.step, right, model, Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, upd]
  exact .more (Part.eq_some_iff.mp exit) <| .done (Part.mem_some _)

example : Cyclic.runSSA model ((left.link right).toCFG 0) (upd (fun _ => 42) default 1) =
    Part.some (.inr 0, 1) := by
  rw [← (left.link right).denote_eq_runSSA model (fun _ => 42) 0 1,
    Graph.denote_link, leftReturns]
  change Prod.map Sum.inr id <$> (pure (0, 0) >>= right.denote model) = _
  rw [pure_bind, rightReturns]
  rfl

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
