module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
import Silmaril.Semantics.Elgot.Thms
import Mathlib.Data.Nat.Pairing

/-! The back edge carries a swap of two live-ins. The header reads both after
the back edge, so sequential moves that clobber either input change the result. -/

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip

open Silmaril.Elgot

private def model : Model Unit Part Nat where
  unit := 0
  pair := Nat.pair
  inl := id
  inr := Nat.succ
  unpair value := pure (Nat.unpair value)
  split
    | 0 => pure (.inl 0)
    | n + 1 => pure (.inr n)
  app _ := pure
  abort _ := Part.none

private theorem pairs : model.PairLawful :=
  ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩

private def registers (control left right : Nat) : Nat → Nat
  | 0 => control
  | 1 => left
  | 2 => right
  | _ => 0

private def header : Block Nat Nat Unit :=
  ⟨0, .term (.case (.val (.var 0)) 0 (.br 99 (.pair (.var 1) (.var 2))) 0 (.br 20 (.var 0)))⟩

private def swapBlock : Block Nat Nat Unit :=
  ⟨0, .let2 1 2 (.val (.pair (.var 2) (.var 1))) (.term (.br 10 .unit))⟩

private def loop : CFG Nat Nat Unit :=
  ⟨.term (.br 10 (.var 0)), [(10, header), (20, swapBlock)]⟩

private def initial : Nat → Nat := registers 1 3 7

private theorem updateControl (control left right next : Nat) :
    upd (registers control left right) 0 next = registers next left right := by
  funext reg
  rcases reg with _ | ⟨_ | ⟨_ | reg⟩⟩ <;> rfl

private theorem swap (control left right : Nat) :
    upd (upd (registers control left right) 1 right) 2 left = registers control right left := by
  funext reg
  rcases reg with _ | ⟨_ | ⟨_ | reg⟩⟩ <;> rfl

private theorem toSwap :
    step model loop.blocks (10, 1, initial) = Part.some (.inr (20, 0, registers 0 3 7)) := by
  simp [step, loop, header, initial, Body.exec, Term.exec, Op.eval, Val.eval,
    updateControl, model, registers]

private theorem backEdge :
    step model loop.blocks (20, 0, registers 0 3 7) = Part.some (.inr (10, 0, registers 0 7 3)) := by
  simp [step, loop, List.lookup, swapBlock, Body.exec, Term.exec, Op.eval, Val.eval,
    updateControl, model, swap, registers]

private theorem toExit :
    step model loop.blocks (10, 0, registers 0 7 3) =
      Part.some (.inr (99, Nat.pair 7 3, registers 0 7 3)) := by
  simp [step, loop, header, Body.exec, Term.exec, Op.eval, Val.eval, updateControl, model, registers]

private theorem exit :
    step model loop.blocks (99, Nat.pair 7 3, registers 0 7 3) =
      Part.some (.inl (99, Nat.pair 7 3, registers 0 7 3)) := rfl

private theorem sourceReturns :
    Cyclic.run model loop initial = Part.some (99, Nat.pair 7 3, registers 0 7 3) := by
  change iter (step model loop.blocks) (10, 1, initial) = Part.some _
  apply Part.eq_some_iff.mpr
  apply (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
  exact .more (Part.eq_some_iff.mp toSwap) <|
    .more (Part.eq_some_iff.mp backEdge) <|
    .more (Part.eq_some_iff.mp toExit) <|
    .done (Part.eq_some_iff.mp exit)

example : obs <$> Cyclic.run model (Versioning.roundTrip loop) initial =
    Part.some (99, Nat.pair 7 3) := by
  rw [Versioning.roundTrip_run_obs model pairs, sourceReturns]
  rfl

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip
