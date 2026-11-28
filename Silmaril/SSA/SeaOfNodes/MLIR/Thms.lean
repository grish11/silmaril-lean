module

public import Silmaril.SSA.SeaOfNodes.MLIR.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.MLIR.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.MLIR

open RVSDG (Origin Tuple Locals Wires extend)
open Diamond (Dataflow Val ValueSort dataPorts sortValue)
open Silmaril.MLIR.Pure (Code Eval OpSignature)
open Lowering
open Silmaril.MLIR.Arith (Env Width)

namespace Lowering

variable {Γ : List Width} {args : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}
variable {s : ValueSort Width} {v : Width}

theorem inputs_agree (env : Env Γ) : NamesAgree env (inputNames Γ) (sourceInputs env) :=
  Proofs.inputs_agree env

theorem weaken_names {ports : List (Diamond.Ty Width)} {env : Env Γ}
    {names : Tuple (Names Γ) ports} {values : Tuple (Val Word) ports}
    (ok : NamesAgree env names values) (value : Word v) :
    NamesAgree (.cons value env) (names.map (weaken v)) values :=
  Proofs.weaken_names ok value

theorem Scope.Agrees.resolve {scope : Scope args past Γ} {env : Env Γ}
    {entry : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env entry locals) (wire : Origin args past (.value s)) :
    env.get (scope.resolveValue wire) = valueBits (Diamond.read model wire entry locals) :=
  Proofs.resolve_correct ok wire

/-- A typed operand vector reads the encoded values of the corresponding wires. -/
theorem Scope.Agrees.operands_eval {scope : Scope args past Γ} {env : Env Γ}
    {entry : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env entry locals) {ins : List (ValueSort Width)}
    (wires : Wires args past (dataPorts ins)) :
    (operands scope wires).eval env = encodeValues (wires.read entry locals) :=
  Proofs.operands_correct ok wires

variable {Source : Diamond.Signature Width} {Target : OpSignature} {Term : List Width → Type} {A : Type}

/-- If the emitted symbols implement the source primitives, the block's
terminator sees the values in the source table's final producer environment. -/
theorem lowerCode_eval (opcode : OpcodeMap Source Target) (evalOp : Eval Target)
    (run : ∀ {ins out}, Source ins out → Tuple (Val Word) (dataPorts ins) → sortValue Word out)
    (agreesOnOpcode : ∀ {ins out} (op : Source ins out) (values : Tuple (Val Word) (dataPorts ins)),
      evalOp (opcode op) (encodeValues values) = valueBits (run op values))
    (flow : Dataflow Source args past sigs) (scope : Scope args past Γ) (env : Env Γ)
    (entry : Tuple (Val Word) args) (locals : Locals (Val Word) past)
    (ok : scope.Agrees env entry locals)
    (terminator : ∀ {Δ}, Scope args (extend past sigs) Δ → Term Δ)
    (finish : ∀ {Δ}, Term Δ → Env Δ → A) (result : A)
    (done : ∀ {Δ} (finalScope : Scope args (extend past sigs) Δ) (finalEnv : Env Δ),
      finalScope.Agrees finalEnv entry (flow.eval ⟨Word, run⟩ entry locals) →
        finish (terminator finalScope) finalEnv = result) :
    (lowerCode opcode flow scope terminator).eval evalOp finish env = result :=
  Proofs.lowerCode_eval opcode evalOp run agreesOnOpcode flow scope env entry locals ok terminator finish result done

end Lowering

/-- The lowered block returns the value of the selected source wire on every
typed input, using the existing Sea of Nodes producer-table evaluator. -/
theorem lower_denote {Γ : List Width} {sigs : List (List (Diamond.Ty Width))} {w : Width}
    (flow : Dataflow Op (inputPorts Γ) [] sigs)
    (result : Origin (inputPorts Γ) (extend [] sigs) (.value (.data w))) (env : Env Γ) :
    (lower flow result).denote env =
      Diamond.read model result (sourceInputs env) (flow.eval model (sourceInputs env) PUnit.unit) :=
  Proofs.lower_denote flow result env

end Silmaril.SSA.SeaOfNodes.MLIR
