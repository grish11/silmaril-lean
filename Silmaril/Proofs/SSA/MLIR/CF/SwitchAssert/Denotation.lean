module

public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.Proofs.MLIR.CF.SwitchAssert

open Silmaril.MLIR
open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)
open CF.SwitchAssert (Block Cfg Outcome)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result Γ : List Width}

private theorem runFor_eq_ofOption_runBlock (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (fuel : Nat) (block : Block Op Label Result Γ) (env : Env Γ) :
    Elgot.Part.runFor (fun state => Part.some (cfg.step evalOp input state)) fuel ⟨Γ, block, env⟩ =
      Part.ofOption (cfg.runBlock evalOp input fuel block env) := by
  induction fuel generalizing Γ with
  | zero => rfl
  | succ fuel ih =>
      simp only [Elgot.Part.runFor, Cfg.step, Cfg.runBlock]
      change (Part.some _).bind _ = _
      rw [Part.bind_some]
      cases block.eval evalOp env with
      | none => rfl
      | some result =>
          cases result with
          | inl next => exact ih (cfg.block next.label) (next.args.append input)
          | inr values => rfl

theorem runFor_eq_ofOption_run (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (fuel : Nat) (input : Env Input) :
    Elgot.Part.runFor (fun state => Part.some (cfg.step evalOp input state)) fuel
        ⟨Input, cfg.entry, input⟩ = Part.ofOption (cfg.run evalOp fuel input) :=
  runFor_eq_ofOption_runBlock cfg evalOp input fuel cfg.entry input

theorem mem_denotePart_iff (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) (outcome : Outcome Result) :
    outcome ∈ cfg.denotePart evalOp input ↔ ∃ fuel, cfg.run evalOp fuel input = some outcome := by
  unfold Cfg.denotePart
  rw [Elgot.Part.mem_iter_iff_exists_fuel]
  simp only [runFor_eq_ofOption_run, Part.mem_ofOption, Option.mem_def]

theorem denotePart_eq_none_iff (cfg : Cfg Op Label Input Result) (evalOp : Eval Op)
    (input : Env Input) : cfg.denotePart evalOp input = Part.none ↔ cfg.Diverges evalOp input := by
  rw [Part.eq_none_iff]
  constructor
  · intro noOutcome fuel
    cases run : cfg.run evalOp fuel input with
    | none => rfl
    | some outcome =>
        have mem := (mem_denotePart_iff cfg evalOp input outcome).mpr ⟨fuel, run⟩
        exact (noOutcome outcome mem).elim
  · intro diverges outcome mem
    obtain ⟨fuel, run⟩ := (mem_denotePart_iff cfg evalOp input outcome).mp mem
    rw [diverges fuel] at run
    cases run

end Silmaril.Proofs.MLIR.CF.SwitchAssert
