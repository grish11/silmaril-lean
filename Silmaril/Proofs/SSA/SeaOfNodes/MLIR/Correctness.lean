module

public import Silmaril.SSA.SeaOfNodes.MLIR.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.MLIR.Proofs

open RVSDG (Port Tuple Origin Wires Locals extend)
open Diamond (Dataflow Val ValueSort dataPorts sortValue)
open Silmaril.MLIR.Arith (Block Env Width)
open Lowering
open Silmaril.MLIR.Pure (Code Eval OpSignature Operands)

variable {Γ : List Width} {args : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}
variable {w v : Width} {s : ValueSort Width}

private theorem get_map {ports : List (Diamond.Ty Width)} {t : Diamond.Ty Width}
    (names : Tuple (Names Γ) ports) (p : Port ports t) :
    (names.map (weaken v)).get p = weaken v t (names.get p) := by
  induction p with
  | head => cases names; rfl
  | tail p ih => cases names with | cons _ tail => exact ih tail

private theorem weaken_get {ports : List (Diamond.Ty Width)} (names : Tuple (Names Γ) ports)
    (p : Port ports (.value s)) (env : Env Γ) (value : Word v) :
    (Env.cons value env).get ((names.map (weaken v)).get p) = env.get (names.get p) := by
  rw [get_map]
  rfl

theorem inputs_agree (env : Env Γ) : NamesAgree env (inputNames Γ) (sourceInputs env) := by
  induction env with
  | nil => intro _ p; cases p
  | cons value env ih =>
    intro _ p
    cases p with
    | head => rfl
    | tail p => exact (weaken_get _ p env value).trans (ih p)

private theorem locals_get (env : Env Γ) (names : Locals (Names Γ) past)
    (values : Locals (Val Word) past) (h : LocalsAgree env names values) (i : Fin past.length) :
    NamesAgree env (names.get i) (values.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons ports tail ih =>
    exact Fin.cases h.1 (fun j => ih names.2 values.2 h.2 j) i

private theorem push_agree (env : Env Γ) (names : Locals (Names Γ) past)
    (values : Locals (Val Word) past) (h : LocalsAgree env names values) (value : sortValue Word s) :
    LocalsAgree (.cons (valueBits value) env) (pushValue s names) (values.snoc (.cons value .nil)) := by
  induction past with
  | nil =>
    refine ⟨?_, trivial⟩
    intro _ p
    cases p with
    | head => rfl
    | tail p => cases p
  | cons _ _ ih =>
    exact ⟨fun p => (weaken_get _ p env (valueBits value)).trans (h.1 p), ih names.2 values.2 h.2⟩

theorem weaken_names {ports : List (Diamond.Ty Width)} {env : Env Γ}
    {names : Tuple (Names Γ) ports} {values : Tuple (Val Word) ports}
    (ok : NamesAgree env names values) (value : Word v) :
    NamesAgree (.cons value env) (names.map (weaken v)) values :=
  fun p => (weaken_get names p env value).trans (ok p)

theorem resolve_correct {scope : Scope args past Γ} {env : Env Γ}
    {entry : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env entry locals) (wire : Origin args past (.value s)) :
    env.get (scope.resolveValue wire) = valueBits (Diamond.read model wire entry locals) := by
  cases wire with
  | arg p => exact ok.inputsAgree p
  | output i p => exact locals_get env scope.locals locals ok.localsAgree i p

private theorem push_scope {scope : Scope args past Γ} {env : Env Γ}
    {entry : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env entry locals) (value : sortValue Word s) :
    (scope.pushValue s).Agrees (.cons (valueBits value) env) entry
      (locals.snoc (.cons value .nil)) :=
  ⟨weaken_names ok.inputsAgree (valueBits value), push_agree env scope.locals locals ok.localsAgree value⟩

theorem operands_correct {scope : Scope args past Γ} {env : Env Γ}
    {entry : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env entry locals) {ins : List (ValueSort Width)}
    (wires : Wires args past (dataPorts ins)) :
    (operands scope wires).eval env = encodeValues (wires.read entry locals) := by
  induction ins with
  | nil => cases wires; rfl
  | cons s ins ih =>
    cases wires with
    | cons wire rest =>
      change Env.cons (env.get (scope.resolveValue wire)) ((operands scope rest).eval env) =
        Env.cons (valueBits (Diamond.read model wire entry locals)) (encodeValues (Wires.read rest entry locals))
      rw [resolve_correct ok wire, ih rest]

variable {Source : Diamond.Signature Width} {Target : OpSignature} {Term : List Width → Type} {A : Type}

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
    (lowerCode opcode flow scope terminator).eval evalOp finish env = result := by
  induction flow generalizing Γ with
  | nil => exact done scope env ok
  | cons op wires rest ih =>
    simp only [lowerCode, Code.eval, operands_correct ok, agreesOnOpcode]
    exact ih _ _ _ (push_scope ok (run op (wires.read entry locals))) terminator done

private theorem emit_correct (scope : Scope args past Γ) (env : Env Γ)
    (entry : Tuple (Val Word) args) (locals : Locals (Val Word) past)
    (hi : NamesAgree env scope.inputs entry) (hl : LocalsAgree env scope.locals locals)
    {ins : List (Diamond.ValueSort Width)} (op : Op ins (.data w))
    (wires : Wires args past (dataPorts ins)) :
    (emit scope op wires).denote env = model.run op (wires.read entry locals) := by
  cases op with
  | constant value => cases wires; rfl
  | binary op =>
    cases wires with | cons x tail =>
    cases tail with | cons y tail =>
    cases tail
    have hx : env.get (scope.resolve x) = Diamond.read model x entry locals :=
      resolve_correct ⟨hi, hl⟩ x
    have hy : env.get (scope.resolve y) = Diamond.read model y entry locals :=
      resolve_correct ⟨hi, hl⟩ y
    change op.denote (env.get (scope.resolve x)) (env.get (scope.resolve y)) = _
    rw [hx, hy]
    cases op <;> rfl

private theorem lowerFrom_correct (flow : Dataflow Op args past sigs)
    (scope : Scope args past Γ) (env : Env Γ)
    (entry : Tuple (Val Word) args) (locals : Locals (Val Word) past)
    (hi : NamesAgree env scope.inputs entry) (hl : LocalsAgree env scope.locals locals)
    (result : Origin args (extend past sigs) (.value (.data w))) :
    (lowerFrom flow scope result).denote env =
      Diamond.read model result entry (flow.eval model entry locals) := by
  induction flow generalizing Γ with
  | nil => exact resolve_correct ⟨hi, hl⟩ result
  | cons op wires rest ih =>
    cases op <;>
      (simp only [lowerFrom, Block.denote, Dataflow.eval, emit_correct scope env entry locals hi hl]
       apply ih
       · exact fun p => (weaken_get _ p _ _).trans (hi p)
       · exact push_agree (s := .data _) _ _ _ hl _)

theorem lower_denote (flow : Dataflow Op (inputPorts Γ) [] sigs)
    (result : Origin (inputPorts Γ) (extend [] sigs) (.value (.data w))) (env : Env Γ) :
    (lower flow result).denote env =
      Diamond.read model result (sourceInputs env) (flow.eval model (sourceInputs env) PUnit.unit) :=
  lowerFrom_correct flow _ env (sourceInputs env) PUnit.unit (inputs_agree env) trivial result

end Silmaril.SSA.SeaOfNodes.MLIR.Proofs
