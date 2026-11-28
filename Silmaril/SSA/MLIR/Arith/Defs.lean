module

public import Init.Data.BitVec
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-! # Scalar MLIR-style arithmetic

Scalar `arith.constant`, `arith.addi`, `arith.subi` and `arith.muli` on
positive-width signless integers. The binary operations have empty overflow
flags. Blocks bind each operation's single result once and return one value.
A scoped application may evaluate a single-block region with one argument and
one yield.
-/

@[expose] public section

namespace Silmaril.MLIR.Arith

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

abbrev Width := { n : Nat // 0 < n }

/-- A reference to an earlier definition or block argument, newest first. -/
inductive Var : List Width → Width → Type where
  | here {Γ : List Width} {w : Width} : Var (w :: Γ) w
  | there {Γ : List Width} {w v : Width} : Var Γ w → Var (v :: Γ) w

/-- The corresponding LambdaSSA de Bruijn index. -/
def Var.index {Γ : List Width} {w : Width} : Var Γ w → Nat
  | .here => 0
  | .there x => x.index + 1

/-- A value assignment for exactly the given context. -/
inductive Env : List Width → Type where
  | nil : Env []
  | cons {Γ : List Width} {w : Width} : BitVec w.val → Env Γ → Env (w :: Γ)

def Env.get {Γ : List Width} {w : Width} (env : Env Γ) : Var Γ w → BitVec w.val
  | .here => let .cons a _ := env; a
  | .there x => let .cons _ env := env; env.get x

/-- Binary scalar operations with modular semantics. -/
inductive BinOp where
  | addi
  | subi
  | muli

def BinOp.denote (op : BinOp) {w : Nat} (x y : BitVec w) : BitVec w :=
  match op with
  | .addi => x + y
  | .subi => x - y
  | .muli => x * y

/-- A primitive application consumes only existing SSA values. -/
inductive Rhs (Γ : List Width) (w : Width) where
  | constant (value : BitVec w.val)
  | binary (op : BinOp) (lhs rhs : Var Γ w)

def Rhs.denote {Γ : List Width} {w : Width} (rhs : Rhs Γ w) (env : Env Γ) : BitVec w.val :=
  match rhs with
  | .constant value => value
  | .binary op x y => op.denote (env.get x) (env.get y)

/-- A single-result SSA block. In `letRegion`, the isolated body sees only
its explicit parameter. Its yield binds a fresh name in the outer block.
Omitting `letRegion` gives the straight-line fragment. -/
inductive Block : List Width → Width → Type where
  | yield {Γ : List Width} {w : Width} (result : Var Γ w) : Block Γ w
  | letOp {Γ : List Width} {v w : Width} (rhs : Rhs Γ v) (rest : Block (v :: Γ) w) :
      Block Γ w
  | letRegion {Γ : List Width} {v a w : Width} (arg : Var Γ a) (body : Block [a] v)
      (rest : Block (v :: Γ) w) : Block Γ w

/-- Denote a block as a total function from its typed environment to its result. -/
def Block.denote {Γ : List Width} {w : Width} : Block Γ w → Env Γ → BitVec w.val
  | .yield x, env => env.get x
  | .letOp rhs rest, env => rest.denote (.cons (rhs.denote env) env)
  | .letRegion arg body rest, env =>
      rest.denote (.cons (body.denote (.cons (env.get arg) .nil)) env)

/-- LambdaSSA atoms retain their bit width. -/
abbrev Atom := (w : Width) × BitVec w.val

def word {w : Width} (value : BitVec w.val) : Value Atom := .atom ⟨w, value⟩

/-- Extend an ambient LambdaSSA environment by a typed environment. At the
top level, out-of-context indices are filled with unit. -/
def Env.toLambdaSSA {Γ : List Width} (env : Env Γ)
    (tail : Semantics.Env Atom := fun _ => .unit) : Semantics.Env Atom :=
  match env with
  | .nil => tail
  | .cons value env => extend (env.toLambdaSSA tail) (word value)

inductive Prim where
  | constant (w : Width) (value : BitVec w.val)
  | binary (op : BinOp) (w : Width)

instance : HasTy Prim (Ty Width) where
  src
    | .constant .. => .unit
    | .binary _ w => .product (.base w) (.base w)
  trg
    | .constant w _ | .binary _ w => .base w

/-- Read a runtime atom at a specified width. -/
def readWord (w : Width) : Value Atom → Option (BitVec w.val)
  | .atom ⟨v, bits⟩ => if same : v = w then some (same ▸ bits) else none
  | _ => none

/-- A primitive can step only on values of its declared operand shape and widths. -/
def Prim.run : Prim → Value Atom → Option (Value Atom)
  | .constant _ value, .unit => some (word value)
  | .binary op w, .pair x y => do
      let x ← readWord w x
      let y ← readWord w y
      pure (word (op.denote x y))
  | _, _ => none

/-- The state-free instruction relation used by both target calculi. -/
def instr (op : Prim) (arg : Value Atom) (_ : Unit) (result : Value Atom) (_ : Unit) : Prop :=
  op.run arg = some result

def Rhs.toLambdaSSA {Γ : List Width} {w : Width} : Rhs Γ w → Tm Prim
  | .constant value => .op (.constant w value) .unit
  | .binary op x y => .op (.binary op w) (.pair (.var x.index) (.var y.index))

/-- Lower a block to a LambdaSSA term. An isolated region becomes an inner
lexical let for the argument. The result of that term is bound by an outer let. -/
def Block.toTerm {Γ : List Width} {w : Width} : Block Γ w → Tm Prim
  | .yield x => .var x.index
  | .letOp rhs rest => .let₁ rhs.toLambdaSSA rest.toTerm
  | .letRegion arg body rest => .let₁ (.let₁ (.var arg.index) body.toTerm) rest.toTerm

/-- Lower a block to a single LambdaSSA exit carrying the result. -/
def Block.toLambdaSSA {Γ : List Width} {w : Width} (block : Block Γ w) : Region Prim :=
  .br 0 block.toTerm

end Silmaril.MLIR.Arith
