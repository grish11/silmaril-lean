module

import Silmaril.SSA.MLIR.SCF.LetIter.FixedProfile.Thms

/-! A typed opcode map, an admitted noncanonical program, and two distinct outcomes. -/

namespace Silmaril.MLIR.SCF.LetIter.FixedProfile.Examples

open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.Pure (Eval i1)
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open CategoryTheory

private def wireProfile : Profile := ⟨[i1], [i1], [i1, i1], [i1]⟩

private inductive SourceOp : List Width → Width → Type
  | probe : SourceOp [] i1

private inductive TargetOp : List Width → Width → Type
  | markedProbe (again : Bool) : TargetOp [] i1

private def source : Signature := ⟨SourceOp⟩
private def target : Signature := ⟨TargetOp⟩

private def renameProbe (again : Bool) : Signature.Renaming source target where
  opcode
    | .probe => .markedProbe again

private def evaluate : Eval target.op
  | _, _, .markedProbe again, .nil => if again then 1 else 0

private def keepPayload : Scalar wireProfile source where
  init := .cons .here .nil
  before := .letOp .probe .nil
    (.terminator (.condition .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
  afterRegion := .terminator (.yield (.cons .here .nil))
  parent := .terminator (.ret (.cons (.there .here) .nil))

private def wiring : (t : Term wireProfile source .program) × Grammar wireProfile source .program t :=
  ⟨_, .wire (.sequence
    (.iterate (.initializer keepPayload.init)
      (.branch (.wire (.condition keepPayload.before)) (.yield keepPayload.afterRegion)))
    (.parent keepPayload.parent))⟩

private def wiredProgram : Native wireProfile source := ⟨wiring.1, ⟨wiring.2⟩⟩

/-- The identity binding at the outermost exit distinguishes the syntax
from every direct encoding. There is another identity binding in the condition. -/
example (p : Scalar wireProfile source) : wiredProgram ≠ encode p := by
  intro h
  have terms := congrArg Subtype.val h
  cases (Tm.let₁.inj terms).2

/-- Decoding the noncanonical program recovers the same observable class. -/
example : (Quotient.mk'' wiredProgram : NativeProgram wireProfile source) =
    encodeQ (Quotient.mk'' keepPayload) := by
  apply Quotient.sound
  intro M input
  exact (observe_of_derivation wiredProgram wiring.2 M input).trans (observe_encode keepPayload M input).symm

private def initial : Env wireProfile.input := .cons 1 .nil

example : Answer.ret (.cons 1 .nil) ∈ (keepPayload.rename (renameProbe false)).observe evaluate initial :=
  ⟨1, rfl⟩

example : Answer.diverge ∈ (keepPayload.rename (renameProbe true)).observe evaluate initial := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ _ ih => exact ih

example :
    (wiredProgram.rename (renameProbe false)).observe evaluate initial =
      wiredProgram.observe (reduct (renameProbe false) evaluate) initial :=
  Native.observe_rename (renameProbe false) wiredProgram evaluate initial

end Silmaril.MLIR.SCF.LetIter.FixedProfile.Examples
