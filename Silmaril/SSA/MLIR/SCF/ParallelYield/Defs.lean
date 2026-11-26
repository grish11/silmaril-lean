module

public import Silmaril.SSA.MLIR.SCF.Parallel.Defs
public import Silmaril.SSA.MLIR.SCF.While.Defs

/-! Typed structural exits for a pure scalar parallel-reduction boundary. -/

@[expose] public section

namespace Silmaril.MLIR.SCF.ParallelYield

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature)

/-- A one-shot region with an explicit argument prefix and a fixed capture suffix.
Its terminal yield transfers a typed tuple to the enclosing construct. -/
abbrev YieldRegion (Op : OpSignature) (Args Captures Result : List Width) :=
  Code Op (Yield Result) (Args ++ Captures)

variable {Op : OpSignature} {Args Captures Result Slots Γ : List Width} {w : Width}

def YieldRegion.run (region : YieldRegion Op Args Captures Result) (evalOp : Eval Op)
    (args : Env Args) (captures : Env Captures) : Env Result :=
  region.eval evalOp Yield.eval (args.append captures)

/-- Expose the same tuple at a fragment boundary by changing the terminator. -/
def YieldRegion.asReturn (region : YieldRegion Op Args Captures Result) :
    Code Op (Return Result) (Args ++ Captures) :=
  region.mapTerm (fun | .yield values => .ret values)

/-- The parallel body terminator supplies one contribution per reduction slot. -/
inductive Reduce (Slots Scope : List Width) where
  | reduce (values : Operands Scope Slots)

def Reduce.eval (term : Reduce Slots Γ) (env : Env Γ) : Env Slots :=
  match term with
  | .reduce values => values.eval env

/-- The combiner terminator returns one value at its slot width. -/
inductive ReduceReturn (width : Width) (Scope : List Width) where
  | ret (value : Var Scope width)

def ReduceReturn.eval (term : ReduceReturn w Γ) (env : Env Γ) : BitVec w.val :=
  match term with
  | .ret value => env.get value

/-- Combiner parameters and result have the same width. The remaining scope
consists of parent captures, with no iteration-local scope. -/
abbrev Combiner (Op : OpSignature) (Captures : List Width) (w : Width) :=
  Code Op (ReduceReturn w) (w :: w :: Captures)

def Combiner.run (combine : Combiner Op Captures w) (evalOp : Eval Op)
    (captures : Env Captures) (left right : BitVec w.val) : BitVec w.val :=
  combine.eval evalOp ReduceReturn.eval (.cons left (.cons right captures))

/-- The combiner region list and contribution tuple have the same ordered slot types. -/
inductive Combiners (Op : OpSignature) (Captures : List Width) : List Width → Type where
  | nil : Combiners Op Captures []
  | cons {w : Width} {slots : List Width} (head : Combiner Op Captures w)
      (tail : Combiners Op Captures slots) : Combiners Op Captures (w :: slots)

def Combiners.eval (evalOp : Eval Op) (captures : Env Captures) :
    {slots : List Width} → Combiners Op Captures slots → Env slots → Env slots → Env slots
  | _, .nil, .nil, .nil => .nil
  | _, .cons head tail, .cons left leftTail, .cons right rightTail =>
      .cons (head.run evalOp captures left right) (tail.eval evalOp captures leftTail rightTail)

/-- The two algebraic laws for every slot at the supplied parent capture assignment. -/
def Combiners.Laws (evalOp : Eval Op) (captures : Env Captures) :
    {slots : List Width} → Combiners Op Captures slots → Prop
  | _, .nil => True
  | _, .cons head tail =>
      Std.Associative (head.run evalOp captures) ∧ Std.Commutative (head.run evalOp captures) ∧
        tail.Laws evalOp captures

/-- Statically admitted, one-dimensional unsigned induction. The iteration body
receives the induction value and parent captures. The continuation receives
the reduced tuple and those same captures, then structurally yields its result. -/
structure Program (Op : OpSignature) (Captures Result : List Width) where
  indexWidth : Width
  space : Parallel.IndexSpace
  stepFits : space.step < 2 ^ indexWidth.val
  exitFits : space.exitIndex < 2 ^ indexWidth.val
  Slots : List Width
  initial : Operands Captures Slots
  body : Code Op (Reduce Slots) (indexWidth :: Captures)
  combiners : Combiners Op Captures Slots
  continuation : YieldRegion Op Slots Captures Result

def Program.indexValue (program : Program Op Captures Result) (index : Nat) :
    BitVec program.indexWidth.val :=
  BitVec.ofNat program.indexWidth.val index

/-- Interpret the typed reduction regions in the pure result model. -/
def Program.reduction (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) : Parallel.Reduction (Env program.Slots) where
  initial := program.initial.eval captures
  contribution index :=
    program.body.eval evalOp Reduce.eval (.cons (program.indexValue index) captures)
  combine := program.combiners.eval evalOp captures

/-- The increasing left fold followed by the enclosing region's structural yield. -/
def Program.denote (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) : Env Result :=
  program.continuation.run evalOp ((program.reduction evalOp captures).denote program.space) captures

/-- Pass each possible pure reduction result to the structural continuation. -/
def Program.Returns (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (result : Env Result) : Prop :=
  ∃ values, (program.reduction evalOp captures).Returns program.space values ∧
    program.continuation.run evalOp values captures = result

end Silmaril.MLIR.SCF.ParallelYield
