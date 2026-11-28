module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

/-! # Shared constructor values and compatible primitive observations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport

open Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous (Family Opcode)

abbrev RawAtom := PUnit.{2}
abbrev RawValue := Value RawAtom

/-- Constructor codes contain no atoms. Their erased values keep each sum tag. -/
def encode : (c : Code) → c.Large → RawValue
  | .unit, _ => .unit
  | .sum l _, .inl v => .inl (encode l v)
  | .sum _ r, .inr v => .inr (encode r v)

/-- Read only the erased constructor values admitted by the given code. -/
def decode : (c : Code) → RawValue → Option c.Large
  | .unit, .unit => some PUnit.unit
  | .sum l _, .inl v => (decode l v).map Sum.inl
  | .sum _ r, .inr v => (decode r v).map Sum.inr
  | _, _ => none

theorem decode_encode (c : Code) (v : c.Large) : decode c (encode c v) = some v := by
  induction c with
  | unit => cases v; rfl
  | sum l r il ir => cases v <;> simp only [encode, decode, il, ir] <;> rfl

/-- Use the same event family and compare each primitive on its declared
input. The raw handler may behave differently on out-of-profile values. -/
def Compatible {n : Nat} {F : Family n} {Events : Type → Type}
    (instr : InstructionModel (Ty.denote (Lifted carriers)) (Opcode F) (ITree.Tree Events))
    (raw : Primitive Events (Opcode F) RawAtom) : Prop :=
  ∀ f x, raw f (encode f.argCode x) =
    (instr.eval f x >>= fun y => pure (encode f.replyCode y))

variable {n : Nat} {F : Family n} {I O : Code} {Events : Type → Type}

/-- Extend a typed handler to the erased constructors. Malformed inputs
have no observation in this instance of the erased interpreter. -/
def rawInstructions
    (instr : InstructionModel (Ty.denote (Lifted carriers)) (Opcode F) (ITree.Tree Events)) :
    Primitive Events (Opcode F) RawAtom := fun f v =>
  match decode f.argCode v with
  | some x => instr.eval f x >>= fun y => pure (encode f.replyCode y)
  | none => ITree.diverge

theorem rawInstructions_compatible
    (instr : InstructionModel (Ty.denote (Lifted carriers)) (Opcode F) (ITree.Tree Events)) :
    Compatible instr (rawInstructions instr) := by
  intro f x
  simp only [rawInstructions, decode_encode]

/-- Evaluate a typed finite step in order, retaining the same instruction
handler and both tags of a loop control result. -/
def Step.denote (instr : InstructionModel (Ty.denote (Lifted carriers)) (Opcode F) (ITree.Tree Events)) :
    {I : Code} → Step F I O → I.Large → ITree.Tree Events O.Large
  | _, .lit x, _ => pure (O.raise x)
  | _, .call f x k, _ => instr.eval f (f.argCode.raise x) >>= k.denote instr
  | _, .split l _, .inl x => l.denote instr x
  | _, .split _ r, .inr x => r.denote instr x

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
