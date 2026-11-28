module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Check.Defs

/-! # Read a mixed primitive row before checking its addresses -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedRows

open Sequential
open PureGamma (Op valueCode)
open Wires.Reverse (Vertex readKind)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]

/-- A value row comes from the data-only opcode carrying its own purity
proof. Threaded primitives use the existing ordered label reader. -/
inductive Row (τ Φ ε : Type u) [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε] where
  | value (op : Φ) (bottom : (instrEff op : ε) = ⊥)
  | ordered : Vertex (τ := τ) (Φ := Φ) → Row τ Φ ε

def read : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    NestedTheta.Kind (Op (τ := τ) Φ ε) ins outs → Option (Row τ Φ ε)
  | _, _, .base (.simple (.pure _ _ (.call p h))) => some (.value p.op h)
  | _, _, .base (.simple (.ordered p)) => .ordered <$> readKind (.base (.simple p)) (fun j => j.elim0)
  | _, _, _ => none

/-- Read a local region of primitive rows. The enclosing recognizer checks
the expected row sequence and certifies the recovered wires. -/
def readScope : {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past rows : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Op (τ := τ) Φ ε) args past rows outs → Option (List (Row τ Φ ε))
  | _, _, _, _, .ret _ => some []
  | _, _, _, _, .bind node _ rest => do
    return (← read node.kind) :: (← readScope rest)

abbrev opcodeCode : NestedTheta.Equality.OpcodeCode (Op (τ := τ) Φ ε) :=
  NestedTheta.ExplicitRuntime.PurePrefix.opcodeCode
    (Flat.Numbered.Recognize.opcodeCode (τ := τ) (Φ := Φ)) (valueCode (τ := τ) (Φ := Φ) (ε := ε))

section Certification

variable [DecidableEq τ] [DecidableEq Φ]
variable {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past rows : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Exact comparison of the input and the canonical mixed graph, including
nested tables and all numbered addresses. -/
def decideGraph (canonical actual : NestedTheta.Graph (Op (τ := τ) Φ ε) args past rows outs) :
    Decidable (canonical = actual) :=
  letI : DecidableEq (opcodeCode (τ := τ) (Φ := Φ) (ε := ε)).Key :=
    inferInstanceAs (DecidableEq (Flat.Numbered.Recognize.OpcodeKey τ Φ ⊕ Φ))
  NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ) (ε := ε)) canonical actual

end Certification

variable [DecidableEq τ]

/-- Reconstitute a typed instruction from the opcode and the expected
boundary sorts. -/
def instruction (I O : τ) (op : Φ) : Option (TwoBlock.Instruction Φ I O) :=
  if input : (instrSrc op : τ) = I then
    if output : (instrTrg op : τ) = O then some ⟨op, input, output⟩ else none
  else none

def value (I O : τ) : Row τ Φ ε → Option {p : TwoBlock.Instruction Φ I O // (instrEff p.op : ε) = ⊥}
  | .value op bottom =>
    if input : (instrSrc op : τ) = I then
      if output : (instrTrg op : τ) = O then some ⟨⟨op, input, output⟩, bottom⟩ else none
    else none
  | .ordered _ => none

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedRows
