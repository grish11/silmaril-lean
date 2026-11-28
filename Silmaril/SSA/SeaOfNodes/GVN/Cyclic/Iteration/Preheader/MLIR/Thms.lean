module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR

open Activation (Inputs)
open Builder.Preheader (Native)
open Diamond (ValueSort)
open Pure.SubZero (model word)
open Loop.MLIR.CF (evalOp)
open Silmaril.MLIR.Arith (Env)

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Diamond.Ty Unit))}
variable {g : Native inputs carried entrySigs headerSigs word}
variable {source normalized : Artifact inputs carried}

/-- Entry executes the translated preheader and passes the complete ordered native Phi packet. -/
theorem emit_entry_frame (admitted : emit? g = some source) (input : Inputs model inputs) :
    source.entry.eval evalOp (fun term env => term.eval env) (inputEnv input) =
      .inl ⟨.header, inputEnv (g.initial model input)⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.emit_entry_frame admitted input

/-- The same preheader instructions and ordered entry operands occur in both artifacts. -/
theorem emit_normalized_entry_eq (original : emit? g = some source)
    (edited : emitNormalized? g = some normalized) : normalized.entry = source.entry :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.emit_normalized_entry_eq original edited

/-- CF fuel counts entry, the final header test, and exit in addition to backedges. -/
theorem emit_run (admitted : emit? g = some source) (input : Inputs model inputs) (budget : Nat) :
    source.run evalOp (budget + 3) (inputEnv input) =
      (g.evalBackedges model budget input).map (fun bits : BitVec 64 => Env.cons (w := i64) bits .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.emit_run admitted input budget

theorem emit_returns_iff (admitted : emit? g = some source) (input : Inputs model inputs) (bits : BitVec 64) :
    (∃ fuel, source.run evalOp fuel (inputEnv input) = some (.cons bits .nil)) ↔
      g.Returns model input bits :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.emit_returns_iff admitted input bits

/-- Compare actual source and normalized emissions at every CF block budget. -/
theorem emit_normalized_run_eq (original : emit? g = some source)
    (edited : emitNormalized? g = some normalized) (input : Inputs model inputs) (fuel : Nat) :
    normalized.run evalOp fuel (inputEnv input) = source.run evalOp fuel (inputEnv input) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.emit_normalized_run_eq original edited input fuel

/-- Both emitted CFGs have a finite return of the same word, with a bound for each CFG. -/
theorem emit_normalized_returns_iff (original : emit? g = some source)
    (edited : emitNormalized? g = some normalized) (input : Inputs model inputs) (bits : BitVec 64) :
    (∃ fuel, normalized.run evalOp fuel (inputEnv input) = some (.cons bits .nil)) ↔
      ∃ fuel, source.run evalOp fuel (inputEnv input) = some (.cons bits .nil) := by
  simp only [emit_normalized_run_eq original edited input]

/-- CF divergence here is absence of a finite return at every budget. -/
theorem emit_normalized_diverges_iff (original : emit? g = some source)
    (edited : emitNormalized? g = some normalized) (input : Inputs model inputs) :
    normalized.Diverges evalOp (inputEnv input) ↔ source.Diverges evalOp (inputEnv input) := by
  simp only [Silmaril.MLIR.CF.Cfg.Diverges, emit_normalized_run_eq original edited input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR
