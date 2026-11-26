module

public import Silmaril.SSA.MLIR.CF.Basic.Defs

/-! Typed CF terminators after ordered block bodies with a shared monad. -/

@[expose] public section

namespace Silmaril.MLIR.CF.Ordered

open Arith (Env Width)

universe u v

variable {Label : List Width → Type} {Input Result Γ : List Width}

/-- Follow existing CF frames, sequencing one block interpretation per
unit of fuel in the same monad. Successor arguments precede the invariant
entry arguments. -/
def runBlock {Block : List Width → Type u} {M : Type → Type v} [Monad M]
    (next : ∀ {args}, Label args → Block (args ++ Input))
    (eval : ∀ {scope}, Block scope → Env scope → M (Frame Label ⊕ Env Result))
    (input : Env Input) : Nat → {scope : List Width} → Block scope → Env scope → M (Option (Env Result))
  | 0, _, _, _ => pure none
  | fuel + 1, _, block, env => do
    match ← eval block env with
    | .inl frame => runBlock next eval input fuel (next frame.label) (frame.args.append input)
    | .inr result => pure (some result)

/-- The computed environment of the ordered body supplies the operands
for the existing typed CF terminator. -/
structure Block (Body : List Width → List Width → Type u) (Label : List Width → Type)
    (Γ Result : List Width) where
  {outs : List Width}
  body : Body Γ outs
  terminator : Terminator Label Result outs

def Block.eval {Body : List Width → List Width → Type u} {M : Type → Type v} [Monad M]
    (evalBody : ∀ {ins outs}, Body ins outs → Env ins → M (Env outs))
    (block : Block Body Label Γ Result) (env : Env Γ) : M (Frame Label ⊕ Env Result) := do
  let values ← evalBody block.body env
  pure (block.terminator.eval values)

structure Cfg (Body : List Width → List Width → Type u) (Label : List Width → Type)
    (Input Result : List Width) where
  entry : Block Body Label Input Result
  block : ∀ {args}, Label args → Block Body Label (args ++ Input) Result

def Cfg.run {Body : List Width → List Width → Type u} {M : Type → Type v} [Monad M]
    (cfg : Cfg Body Label Input Result)
    (evalBody : ∀ {ins outs}, Body ins outs → Env ins → M (Env outs))
    (fuel : Nat) (input : Env Input) : M (Option (Env Result)) :=
  runBlock cfg.block (Block.eval evalBody) input fuel cfg.entry input

end Silmaril.MLIR.CF.Ordered
