module

public import Silmaril.SSA.MLIR.SCF.While.Defs

/-! A single pure `scf.for` in the unsigned fixed-width integer profile. -/

@[expose] public section

namespace Silmaril.MLIR.SCF

open Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature i1)

/-- The bounds and step use `unsignedCmp`. The body receives the induction
variable and the carried tuple. The continuation receives the final carried
tuple. Both can capture the parent input. -/
structure For (Op : OpSignature) (Input Result : List Width) where
  width : Width
  widthSupported : width.val ≤ 2 ^ 24 - 1
  Carried : List Width
  lowerBound : Var Input width
  upperBound : Var Input width
  step : Var Input width
  init : Operands Input Carried
  body : Code Op (Yield Carried) (width :: (Carried ++ Input))
  cont : Code Op (Return Result) (Carried ++ Input)

namespace For

variable {Op : OpSignature} {Input Result Γ Δ Carried : List Width} {w : Width}

/-- The ceiling of the nonnegative distance divided by the positive step. -/
def tripCount (loop : For Op Input Result) (input : Env Input) : Nat :=
  let step := (input.get loop.step).toNat
  ((input.get loop.upperBound).toNat - (input.get loop.lowerBound).toNat + (step - 1)) / step

/-- The arbitrary-precision induction value, including the first value at
or beyond the upper bound when the loop exits. -/
def inductionAt (loop : For Op Input Result) (input : Env Input) (j : Nat) : Nat :=
  (input.get loop.lowerBound).toNat + j * (input.get loop.step).toNat

/-- The step is positive, and even the update after the last body fits the
unsigned induction type. A zero-trip loop needs only its initial value. -/
def Admitted (loop : For Op Input Result) (input : Env Input) : Prop :=
  0 < (input.get loop.step).toNat ∧ loop.inductionAt input (loop.tripCount input) < 2 ^ loop.width.val

instance (loop : For Op Input Result) (input : Env Input) : Decidable (loop.Admitted input) := by
  unfold Admitted
  infer_instance

/-- Execute the remaining bodies from index `j`, then execute the parent
continuation once on the final carried tuple. -/
def denoteFrom (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input) :
    Nat → Nat → Env loop.Carried → Env Result
  | 0, _, carried => loop.cont.eval evalOp Return.eval (carried.append input)
  | remaining + 1, j, carried =>
      let iv := BitVec.ofNat loop.width.val (loop.inductionAt input j)
      let next := loop.body.eval evalOp Yield.eval (.cons iv (carried.append input))
      loop.denoteFrom evalOp input remaining (j + 1) next

/-- The finite denotation of the admitted unsigned loop. -/
def denote (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input) : Env Result :=
  loop.denoteFrom evalOp input (loop.tripCount input) 0 (loop.init.eval input)

/-- Check the arithmetic precondition before evaluating the finite loop. -/
def run (loop : For Op Input Result) (evalOp : Eval Op) (input : Env Input) : Option (Env Result) :=
  if loop.Admitted input then some (loop.denote evalOp input) else none

/-- The lowering adds only an unsigned comparison and an increment to the
supplied body and continuation primitives. -/
inductive LowerOp (Op : OpSignature) : OpSignature where
  | original {args : List Width} {w : Width} (op : Op args w) : LowerOp Op args w
  | ult (w : Width) : LowerOp Op [w, w] i1
  | addi (w : Width) : LowerOp Op [w, w] w

def lowerEval (evalOp : Eval Op) : Eval (LowerOp Op)
  | _, _, .original op, args => evalOp op args
  | _, _, .ult _, .cons lhs (.cons rhs .nil) => BitVec.ofBool (lhs.ult rhs)
  | _, _, .addi _, .cons lhs (.cons rhs .nil) => lhs + rhs

inductive Label (w : Width) (Carried : List Width) : List Width → Type where
  | test : Label w Carried (w :: Carried)
  | body : Label w Carried (w :: Carried)
  | exit : Label w Carried Carried

/-- Refer to a captured variable beneath a prefix of block arguments. -/
def weakenVar (ref : Var Γ w) : (args : List Width) → Var (args ++ Γ) w
  | [] => ref
  | _ :: rest => .there (weakenVar ref rest)

def renameOperands (rename : ∀ {w}, Var Γ w → Var Δ w) :
    {types : List Width} → Operands Γ types → Operands Δ types
  | _, .nil => .nil
  | _, .cons head tail => .cons (rename head) (renameOperands rename tail)

/-- The references to the block arguments in order, before any captures. -/
def argumentOperands (Input : List Width) : (args : List Width) → Operands (args ++ Input) args
  | [] => .nil
  | _ :: rest => .cons .here (renameOperands Var.there (argumentOperands Input rest))

def lowerTest (loop : For Op Input Result) :
    CF.Block (LowerOp Op) (Label loop.width loop.Carried) (loop.width :: (loop.Carried ++ Input)) Result :=
  .letOp (.ult loop.width)
    (.cons .here (.cons (weakenVar loop.upperBound (loop.width :: loop.Carried)) .nil)) <|
  .terminator (.condBr .here
    ⟨.body, renameOperands Var.there (argumentOperands Input (loop.width :: loop.Carried))⟩
    ⟨.exit, renameOperands (fun ref => .there (.there ref)) (argumentOperands Input loop.Carried)⟩)

/-- Copy the body operations. Replace its yield with the induction update and
a branch carrying both the updated induction value and the yielded tuple. -/
def lowerBody : {Γ : List Width} → Var Γ w → Var Γ w → Code Op (Yield Carried) Γ →
    CF.Block (LowerOp Op) (Label w Carried) Γ Result
  | _, iv, step, .terminator (.yield values) =>
      .letOp (.addi w) (.cons iv (.cons step .nil)) <|
      .terminator (.br ⟨.test, .cons .here (renameOperands Var.there values)⟩)
  | _, iv, step, .letOp op operands rest =>
      .letOp (.original op) operands (lowerBody (.there iv) (.there step) rest)

def lowerCont : {Γ : List Width} → Code Op (Return Result) Γ →
    CF.Block (LowerOp Op) (Label w Carried) Γ Result
  | _, .terminator (.ret values) => .terminator (.ret values)
  | _, .letOp op operands rest => .letOp (.original op) operands (lowerCont rest)

/-- Lower to an entry, test, body and exit. Both loop edges pass typed block
arguments. The exit receives exactly the loop result tuple. -/
def lower (loop : For Op Input Result) :
    CF.Cfg (LowerOp Op) (Label loop.width loop.Carried) Input Result where
  entry := .terminator (.br ⟨.test, .cons loop.lowerBound loop.init⟩)
  block
    | .test => loop.lowerTest
    | .body => lowerBody .here (weakenVar loop.step (loop.width :: loop.Carried)) loop.body
    | .exit => lowerCont loop.cont

end For

end Silmaril.MLIR.SCF
