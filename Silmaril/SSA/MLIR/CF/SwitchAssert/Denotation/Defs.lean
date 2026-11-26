module

public import Silmaril.SSA.MLIR.CF.SwitchAssert.Defs
public import Silmaril.Semantics.Elgot.Defs

/-! Partial denotation for the typed switch and assertion fragment. -/

@[expose] public section

namespace Silmaril.MLIR.CF.SwitchAssert

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

/-- A block paired with the environment for its scope, ready to execute. -/
abbrev BlockState (Op : OpSignature) (Label : List Width → Type) (Result : List Width) :=
  Σ Γ, Block Op Label Result Γ × Env Γ

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}

/-- Evaluate one block. A successor receives its typed arguments followed by the
original input. A returned tuple or a failed assertion ends iteration. -/
def Cfg.step (cfg : Cfg Op Label Input Result) (evalOp : Eval Op) (input : Env Input) :
    BlockState Op Label Result → Outcome Result ⊕ BlockState Op Label Result
  | ⟨_, block, env⟩ =>
      match block.eval evalOp env with
      | some (.inl next) => .inr ⟨_, cfg.block next.label, next.args.append input⟩
      | some (.inr values) => .inl (.returned values)
      | none => .inl .aborted

/-- Iterate from the entry block. Both terminal outcomes are defined in `Part`. -/
noncomputable def Cfg.denotePart (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) : Part (Outcome Result) :=
  Elgot.iter (fun state => Part.some (cfg.step evalOp input state)) ⟨Input, cfg.entry, input⟩

end Silmaril.MLIR.CF.SwitchAssert
