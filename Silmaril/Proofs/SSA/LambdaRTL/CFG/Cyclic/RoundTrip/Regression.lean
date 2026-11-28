module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison.Thms
import Silmaril.SSA.LambdaRTL.Thms
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

/-! The authored lexical graph uses a control-and-pair packet at label 10
and a plain pair at label 20. Its packets are independent of the compiler's
snapshot layout. -/

private def lexicalHeader : Block (Nat × Nat) Nat Unit :=
  ⟨(0, 5), .let2 (0, 1) (0, 2) (.val (.var (0, 5))) <| .term <|
    .case (.val (.var (0, 1))) (0, 3) (.br 99 (.var (0, 2))) (0, 3) (.br 20 (.var (0, 2)))⟩

private def lexicalSwap : Block (Nat × Nat) Nat Unit :=
  ⟨(1, 7), .let2 (1, 1) (2, 1) (.val (.var (1, 7))) <| .term <|
    .br 10 (.pair .unit (.pair (.var (2, 1)) (.var (1, 1))))⟩

private def lexicalLoop : CFG (Nat × Nat) Nat Unit :=
  ⟨.term (.br 10 (.pair (.var (0, 0)) (.pair (.var (1, 0)) (.var (2, 0))))),
    [(10, lexicalHeader), (20, lexicalSwap)]⟩

private def lexicalInput (reg : Nat × Nat) : Nat :=
  if reg.2 = 0 then initial reg.1 else 42

private theorem lexicalEntrySSA :
    lexicalLoop.entry.toRegion.IsSSA {(0, 0), (1, 0), (2, 0)} := by
  simp [lexicalLoop, Body.toRegion, Term.toRegion, Region.IsSSA, Val.fv, Finset.insert_comm]

private theorem lexicalEntryZero : ∀ reg ∈ lexicalLoop.entry.toRegion.fv, reg.2 = 0 := by
  intro reg used
  have member := Region.fv_subset_of_isSSA lexicalEntrySSA used
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl <;> rfl

private theorem lexicalBlocksSSA (item : Nat × Block (Nat × Nat) Nat Unit)
    (member : item ∈ lexicalLoop.blocks) : item.2.body.toRegion.IsSSA {item.2.param} := by
  simp only [lexicalLoop, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [lexicalHeader, lexicalSwap, Body.toRegion, Term.toRegion, Region.IsSSA, Op.fv, Val.fv]

private theorem lexicalClosed : PacketClosed lexicalLoop :=
  fun item member => Region.fv_subset_of_isSSA (lexicalBlocksSSA item member)

-- Every compiled block has a version-zero parameter, even if its body never reads it.
example : ¬ ∃ source : CFG Nat Nat Unit, Versioning.compile source = lexicalLoop := by
  rintro ⟨source, equal⟩
  have firstParam := congrArg (fun graph : CFG (Nat × Nat) Nat Unit =>
    graph.blocks.head?.map (fun item => item.2.param.2)) equal
  cases source with
  | mk entry blocks =>
    cases blocks <;> simp [Versioning.compile, Versioning.compileBlock, Versioning.compileBlockWith,
      lexicalLoop, lexicalHeader] at firstParam

private theorem lexicalReturns :
    Cyclic.runSSA model lexicalLoop lexicalInput = Part.some (99, Nat.pair 7 3) := by
  have entry : lexicalLoop.entry.evalJump model lexicalInput =
      pure (10, Nat.pair 1 (Nat.pair 3 7)) := rfl
  rw [Cyclic.runSSA, entry, pure_bind]
  have toSwap : Cyclic.stepSSA model lexicalLoop.blocks lexicalInput (10, Nat.pair 1 (Nat.pair 3 7)) =
      Part.some (.inr (20, Nat.pair 3 7)) := by
    simp [Cyclic.stepSSA, lexicalLoop, lexicalHeader, Body.evalJump, Body.exec, Term.exec,
      Op.eval, Val.eval, model, upd]
  have back : Cyclic.stepSSA model lexicalLoop.blocks lexicalInput (20, Nat.pair 3 7) =
      Part.some (.inr (10, Nat.pair 0 (Nat.pair 7 3))) := by
    simp [Cyclic.stepSSA, lexicalLoop, lexicalSwap, List.lookup, Body.evalJump, Body.exec, Term.exec,
      Op.eval, Val.eval, model, upd]
  have toExit : Cyclic.stepSSA model lexicalLoop.blocks lexicalInput (10, Nat.pair 0 (Nat.pair 7 3)) =
      Part.some (.inr (99, Nat.pair 7 3)) := by
    simp [Cyclic.stepSSA, lexicalLoop, lexicalHeader, Body.evalJump, Body.exec, Term.exec,
      Op.eval, Val.eval, model, upd]
  have exit : Cyclic.stepSSA model lexicalLoop.blocks lexicalInput (99, Nat.pair 7 3) =
      Part.some (.inl (99, Nat.pair 7 3)) := rfl
  exact Part.eq_some_iff.mpr ((Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
    (.more (Part.eq_some_iff.mp toSwap) <| .more (Part.eq_some_iff.mp back) <|
      .more (Part.eq_some_iff.mp toExit) <| .done (Part.eq_some_iff.mp exit)))

example : Cyclic.runSSA model (Versioning.compile (deversionGraph lexicalLoop)) lexicalInput =
    Part.some (99, Nat.pair 7 3) := by
  rw [runSSA_deversion_reversion model pairs lexicalLoop lexicalClosed lexicalEntryZero, lexicalReturns]

private def admittedLexicalLoop : Comparison.LexicalGraph Nat Nat Unit :=
  ⟨lexicalLoop, ⟨_, by simp +contextual, lexicalEntrySSA⟩, lexicalBlocksSSA⟩

private noncomputable def lexicalClass : Comparison.SSAClass Nat Nat Unit Part Nat :=
  Quotient.mk _ admittedLexicalLoop

-- The quotient's inverse accepts the handwritten graph and preserves its observed swap.
example : Comparison.rtlClassObserve ⟨model, pairs⟩
    (Comparison.classEquiv.symm lexicalClass) initial = Part.some (99, Nat.pair 7 3) := by
  change Comparison.rtlClassObserve ⟨model, pairs⟩ (Comparison.deversionClass lexicalClass) initial = _
  rw [Comparison.classObserve_deversion]
  change Comparison.ssaObserve ⟨model, pairs⟩ admittedLexicalLoop initial = _
  rw [← Comparison.observe_deversion]
  exact (Comparison.observe_deversion_runSSA ⟨model, pairs⟩ admittedLexicalLoop lexicalInput).trans lexicalReturns

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip
