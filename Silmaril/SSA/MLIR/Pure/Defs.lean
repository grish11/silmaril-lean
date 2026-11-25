module

public import Silmaril.SSA.MLIR.Arith.Defs

/-! Straight-line SSA code with scoped operands and a typed terminator. -/

@[expose] public section

namespace Silmaril.MLIR.Arith

/-- Add a suffix of enclosing values to a block's argument environment. -/
def Env.append {Γ Δ : List Width} : Env Γ → Env Δ → Env (Γ ++ Δ)
  | .nil, tail => tail
  | .cons value env, tail => .cons value (env.append tail)

end Silmaril.MLIR.Arith

namespace Silmaril.MLIR.Pure

open Arith (Width Var Env)

/-- The condition type used by SCF and CF. -/
def i1 : Width := ⟨1, by decide⟩

/-- An ordered tuple of references to values in scope. -/
inductive Operands (Γ : List Width) : List Width → Type where
  | nil : Operands Γ []
  | cons {w : Width} {Δ : List Width} (head : Var Γ w) (tail : Operands Γ Δ) :
      Operands Γ (w :: Δ)

def Operands.eval {Γ Δ : List Width} (env : Env Γ) : Operands Γ Δ → Env Δ
  | .nil => .nil
  | .cons head tail => .cons (env.get head) (tail.eval env)

/-- Operations have explicit operand types and one result. A model interprets
each symbol as a total deterministic function on exactly its operands. -/
abbrev OpSignature := List Width → Width → Type

abbrev Eval (Op : OpSignature) :=
  ∀ {args w}, Op args w → Env args → BitVec w.val

/-- A sequence of typed operation bindings ending in a dialect-specific
terminator. Each binding extends only the rest of the block. -/
inductive Code (Op : OpSignature) (Term : List Width → Type) : List Width → Type where
  | terminator {Γ : List Width} (term : Term Γ) : Code Op Term Γ
  | letOp {Γ args : List Width} {w : Width} (op : Op args w) (operands : Operands Γ args)
      (rest : Code Op Term (w :: Γ)) : Code Op Term Γ

variable {Op : OpSignature} {Term Term' : List Width → Type} {Γ : List Width}

/-- Replace only the terminator, in the scope established by the preceding code. -/
def Code.mapTerm (f : ∀ {Δ}, Term Δ → Term' Δ) : {Γ : List Width} → Code Op Term Γ → Code Op Term' Γ
  | _, .terminator term => .terminator (f term)
  | _, .letOp op args rest => .letOp op args (rest.mapTerm f)

/-- Execute the bindings, then interpret the terminator in the resulting scope. -/
def Code.eval {α : Type} (evalOp : Eval Op) (finish : ∀ {Δ}, Term Δ → Env Δ → α) :
    {Γ : List Width} → Code Op Term Γ → Env Γ → α
  | _, .terminator term, env => finish term env
  | _, .letOp op args rest, env => rest.eval evalOp finish (.cons (evalOp op (args.eval env)) env)

end Silmaril.MLIR.Pure
