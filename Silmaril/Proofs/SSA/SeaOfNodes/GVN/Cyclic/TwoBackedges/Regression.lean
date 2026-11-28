module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Regression

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort dataPorts)
open GVN.Cyclic.TwoBackedges
open Pure.SubZero (BinaryOpcode word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads (Quad)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)
open Silmaril.SSA.RVSDG (Port)

private abbrev regs : List (ValueSort Unit) :=
  [.predicate, .predicate, word, word, word, word, word, word]

private def again : Port (dataPorts regs) (.value .predicate) := .head
private def select : Port (dataPorts regs) (.value .predicate) := .tail .head
private def x : WordSlot regs := .tail (.tail .head)
private def y : WordSlot regs := .tail (.tail (.tail .head))
private def left : WordSlot regs := .tail (.tail (.tail (.tail .head)))
private def right : WordSlot regs := .tail (.tail (.tail (.tail (.tail .head))))
private def resultLeft : WordSlot regs := .tail (.tail (.tail (.tail (.tail (.tail .head)))))
private def resultRight : WordSlot regs := .tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))

private def binary (op : BinaryOpcode) (dest lhs rhs : WordSlot regs) : Quad Opcode regs :=
  ⟨[word, word], word, dest, .arithmetic op, .cons lhs (.cons rhs .nil)⟩

private def stop : Quad Opcode regs := ⟨[], .predicate, again, .boolean false, .nil⟩

private def fixture (reverseFalse : Bool) : Program Opcode regs word where
  preheader := [binary .add left x y, binary .add right x y]
  header := [binary .add resultLeft left x, binary .add resultRight right x]
  again := again
  select := select
  result := resultLeft
  feedback
    | true => [binary .add left resultLeft y, binary .add right resultRight y, stop]
    | false => [binary .sub left resultLeft y,
        if reverseFalse then binary .sub right y resultRight else binary .sub right resultRight y,
        stop]

private def input (side : Bool) (u v : BitVec 64) : Bank (regs := regs) model :=
  .cons ⟨true⟩ (.cons ⟨side⟩ (.cons u (.cons v (.cons 0#64 (.cons 1#64 (.cons 2#64 (.cons 3#64 .nil)))))))

private def rewritten : Program Opcode regs word := { fixture false with result := resultRight }

theorem admitted_redirects_the_actual_result :
    rewrite? (fixture false) left right resultRight = some rewritten ∧
      rewritten.result = resultRight ∧ (fixture false).result = resultLeft :=
  ⟨rfl, rfl, rfl⟩

private def firstFeedback (p : Program Opcode regs word) (entry : Bank (regs := regs) model) :
    Option (Bool × BitVec 64 × BitVec 64) :=
  match p.step model (p.preheader.eval model entry) with
  | .inl _ => none
  | .inr (side, packet) => some (side, packet.get left, packet.get right)

theorem each_feedback_occurrence_executes_its_own_bank :
    firstFeedback (fixture false) (input true 3 4) = some (true, 14, 14) ∧
      firstFeedback (fixture false) (input false 3 4) = some (false, 6, 6) ∧
      firstFeedback rewritten (input true 3 4) = some (true, 14, 14) ∧
      firstFeedback rewritten (input false 3 4) = some (false, 6, 6) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem both_native_graphs_return_after_a_backedge :
    (fixture false).source.runFrom model 4 0 (input true 3 4) = none ∧
      (fixture false).source.runFrom model 5 0 (input true 3 4) = some 17#64 ∧
      rewritten.source.runFrom model 5 0 (input true 3 4) = some 17#64 ∧
      (fixture false).source.runFrom model 5 0 (input false 3 4) = some 9#64 ∧
      rewritten.source.runFrom model 5 0 (input false 3 4) = some 9#64 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem both_native_graphs_wrap_at_the_word_boundary :
    let max : BitVec 64 := 0xffffffffffffffff
    firstFeedback (fixture false) (input true max 1) = some (true, 0, 0) ∧
      (fixture false).source.runFrom model 5 0 (input true max 1) = some max ∧
      rewritten.source.runFrom model 5 0 (input true max 1) = some max :=
  ⟨rfl, rfl, rfl⟩

theorem reversal_on_false_feedback_refuses_the_rewrite :
    entryMatches (fixture true) left right = true ∧
      feedbackMatches (fixture true) left right true = true ∧
      feedbackMatches (fixture true) left right false = false ∧
      exitMatches (fixture true) left right resultRight = true ∧
      rewrite? (fixture true) left right resultRight = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem unchecked_redirect_changes_the_return_after_false_feedback :
    let invalid := { fixture true with result := resultRight }
    (fixture true).source.runFrom model 5 0 (input false 3 4) = some 9#64 ∧
      invalid.source.runFrom model 5 0 (input false 3 4) = some (-3 : BitVec 64) :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Regression
