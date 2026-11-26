module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Correctness
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

/-! Typed MLIR CFG execution preserves and reflects all pure single-loop returns. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF

open SeaOfNodes.MLIR (Word sourceInputs)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Diamond (Val ValueSort dataPorts)
open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

/-- The CF emitter's scalar opcode map implements the source word operations. -/
theorem opcode_eval {ins : List (ValueSort Width)} {out : ValueSort Width}
    (op : Op ins out) (input : Tuple (Val Word) (dataPorts ins)) :
    evalOp (opcode op) (encodeValues input) = valueBits (model.run op input) :=
  Proofs.opcode_correct op input

namespace Bank

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Program Γ carried result entrySigs headerSigs) (input : Env Γ)

/-- Preserves every entry Φ operand in argument order. -/
theorem lower_entry_frame :
    (lower g).entry.eval evalOp (fun term env => term.eval env) input =
      .inl ⟨.header, bankEnv (g.initial model (sourceInputs input))⟩ :=
  Proofs.entry_frame g input

/-- A taken backedge carries the simultaneous native latch. Exit passes
only the result wire to its own block. -/
theorem lower_header_frame (old : Values carried) :
    ((lower g).block .header).eval evalOp (fun term env => term.eval env) ((bankEnv old).append input) =
      .inl (match g.step model (sourceInputs input) old with
        | .inl value => ⟨.exit, .cons value .nil⟩
        | .inr next => ⟨.header, bankEnv next⟩) :=
  Proofs.header_frame g input old

/-- Count entry, the final header test, and exit in addition to backedges. -/
theorem lower_run (budget : Nat) :
    (lower g).run evalOp (budget + 3) input =
      (g.evalBackedges model budget (sourceInputs input)).map (fun value => Env.cons value .nil) :=
  Proofs.run_budget g input budget

theorem lower_returns_iff (value : Word result) :
    g.Returns model (sourceInputs input) value ↔
      ∃ fuel, (lower g).run evalOp fuel input = some (.cons value .nil) :=
  Proofs.returns_iff g input value

theorem lower_denotePart :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  Proofs.denotePart_eq g input

end Bank

private theorem singleton_env {width : Width} (values : Bank.Values [width]) :
    Bank.bankEnv values = .cons (values.get .head) .nil := by
  cases values with | cons value tail => cases tail; rfl

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Program Γ carried result entrySigs headerSigs) (input : Env Γ)

/-- Execute the preheader and route the entry Φ operand to the header. -/
theorem lower_entry_frame :
    (lower g).entry.eval evalOp (fun term env => term.eval env) input =
      .inl ⟨.header, .cons ((g.initial model (sourceInputs input)).get .head) .nil⟩ :=
  Bank.lower_entry_frame g input

/-- One header activation routes the selected successor with its native argument. -/
theorem lower_header_frame (old : Word carried) :
    ((lower g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) =
      .inl (match g.step model (sourceInputs input) (.cons old .nil) with
        | .inl value => ⟨.exit, .cons value .nil⟩
        | .inr next => ⟨.header, .cons (next.get .head) .nil⟩) := by
  have frame := Bank.lower_header_frame g input (.cons old .nil)
  change ((lower g).block .header).eval evalOp (fun term env => term.eval env) (.cons old input) = _ at frame
  cases step : g.step model (sourceInputs input) (.cons old .nil) with
  | inl value => simpa only [step] using frame
  | inr next => simpa only [step, singleton_env] using frame

/-- The entry, final header test and exit account for the three extra blocks. -/
theorem lower_run (budget : Nat) :
    (lower g).run evalOp (budget + 3) input =
      (g.evalBackedges model budget (sourceInputs input)).map (fun value => Env.cons value .nil) :=
  Bank.lower_run g input budget

/-- Each native finite return agrees with some finite execution of the typed CFG,
and every such target return is a native finite return. -/
theorem lower_returns_iff (value : Word result) :
    g.Returns model (sourceInputs input) value ↔
      ∃ fuel, (lower g).run evalOp fuel input = some (.cons value .nil) :=
  Bank.lower_returns_iff g input value

/-- The existing partial CFG denotation returns the source word as a singleton
result vector. Its domain is exactly the native loop's domain. -/
theorem lower_denotePart :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  Bank.lower_denotePart g input

theorem lower_diverges_iff :
    (lower g).Diverges evalOp input ↔ ¬ (g.denote model (sourceInputs input)).Dom := by
  rw [← Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_diverges_iff,
    ← Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_none_iff, lower_denotePart, Part.eq_none_iff']
  rfl

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
