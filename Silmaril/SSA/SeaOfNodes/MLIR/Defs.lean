module

public import Silmaril.SSA.MLIR.Pure.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Defs

/-! # Sea of Nodes pure producers in scalar MLIR

Bind each producer in the existing dependency order. An input or producer
address is resolved to the corresponding in-scope scalar SSA variable.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.MLIR

open RVSDG (Port Tuple Origin Wires Locals extend)
open Diamond (Dataflow Val ValueSort dataPorts sortValue)
open Silmaril.MLIR.Arith (BinOp Block Env Rhs Var Width)

abbrev Word (w : Width) := BitVec w.val

/-- The flag-free scalar operation profiles shared by the pure source and Arith. -/
inductive Op : Diamond.Signature.{0, 0} Width where
  | constant {w : Width} (value : Word w) : Op [] (.data w)
  | binary {w : Width} (op : BinOp) : Op [.data w, .data w] (.data w)

/-- The pure source model on fixed-width words. -/
def model : Diamond.Model Op where
  value := Word
  run
    | .constant value, .nil => value
    | .binary op, .cons x (.cons y .nil) => op.denote x y

abbrev inputPorts (Γ : List Width) : List (Diamond.Ty Width) :=
  dataPorts (Γ.map Diamond.ValueSort.data)

/-- Read the source input ports in the same order as the block arguments. -/
def sourceInputs : {Γ : List Width} → Env Γ → Tuple (Val Word) (inputPorts Γ)
  | _, .nil => .nil
  | _, .cons value tail => .cons value (sourceInputs tail)

namespace Lowering

def valueWidth : ValueSort Width → Width
  | .data w => w
  | .predicate => Silmaril.MLIR.Pure.i1

def valueBits : {s : ValueSort Width} → sortValue Word s → Word (valueWidth s)
  | .data _, x => x
  | .predicate, test => BitVec.ofBool test.down

/-- Scalar SSA names for source values, with predicates represented as `i1`. -/
def Names (Γ : List Width) : Diamond.Ty Width → Type
  | .value s => Var Γ (valueWidth s)
  | _ => PUnit

variable {Γ : List Width} {args : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}

def weaken (v : Width) (t : Diamond.Ty Width) : Names Γ t → Names (v :: Γ) t :=
  match t with
  | .value _ => Var.there
  | .state _ | .control _ => id

def inputNames : (Γ : List Width) → Tuple (Names Γ) (inputPorts Γ)
  | [] => .nil
  | v :: Γ => .cons Var.here ((inputNames Γ).map (weaken v))

structure Scope (args : List (Diamond.Ty Width)) (past : List (List (Diamond.Ty Width))) (Γ : List Width) where
  inputs : Tuple (Names Γ) args
  locals : Locals (Names Γ) past

/-- Extend the name table by one result while retaining all producer numbers. -/
def pushValue (s : ValueSort Width) : {past : List (List (Diamond.Ty Width))} → Locals (Names Γ) past →
    Locals (Names (valueWidth s :: Γ)) (past ++ [[.value s]])
  | [], _ => (.cons Var.here .nil, PUnit.unit)
  | _ :: _, locals => (locals.1.map (weaken (valueWidth s)), pushValue s locals.2)

abbrev pushLocal (v : Width) : {past : List (List (Diamond.Ty Width))} → Locals (Names Γ) past →
    Locals (Names (v :: Γ)) (past ++ [[.value (.data v)]]) :=
  fun {_} locals => pushValue (.data v) locals

def Scope.pushValue (scope : Scope args past Γ) (s : ValueSort Width) :
    Scope args (past ++ [[.value s]]) (valueWidth s :: Γ) :=
  ⟨scope.inputs.map (weaken (valueWidth s)), Lowering.pushValue s scope.locals⟩

def Scope.push (scope : Scope args past Γ) (v : Width) :
    Scope args (past ++ [[.value (.data v)]]) (v :: Γ) :=
  scope.pushValue (.data v)

def Scope.resolveValue (scope : Scope args past Γ) {s : ValueSort Width} :
    Origin args past (.value s) → Var Γ (valueWidth s)
  | .arg port => scope.inputs.get port
  | .output i port => (scope.locals.get i).get port

def Scope.resolve (scope : Scope args past Γ) {w : Width}
    (wire : Origin args past (.value (.data w))) : Var Γ w :=
  scope.resolveValue wire

def NamesAgree (env : Env Γ) {ports : List (Diamond.Ty Width)}
    (names : Tuple (Names Γ) ports) (values : Tuple (Val Word) ports) : Prop :=
  ∀ {s : ValueSort Width} (p : Port ports (.value s)), env.get (names.get p) = valueBits (values.get p)

def LocalsAgree (env : Env Γ) : {past : List (List (Diamond.Ty Width))} →
    Locals (Names Γ) past → Locals (Val Word) past → Prop
  | [], _, _ => True
  | _ :: _, names, values => NamesAgree env names.1 values.1 ∧ LocalsAgree env names.2 values.2

structure Scope.Agrees (scope : Scope args past Γ) (env : Env Γ)
    (inputs : Tuple (Val Word) args) (locals : Locals (Val Word) past) : Prop where
  inputsAgree : NamesAgree env scope.inputs inputs
  localsAgree : LocalsAgree env scope.locals locals

open Silmaril.MLIR.Pure (Code Operands OpSignature)

def operands (scope : Scope args past Γ) : {ins : List (ValueSort Width)} →
    Wires args past (dataPorts ins) → Operands Γ (ins.map valueWidth)
  | [], .nil => .nil
  | _ :: _, .cons wire rest => .cons (scope.resolveValue wire) (operands scope rest)

def encodeValues : {ins : List (ValueSort Width)} →
    Tuple (Val Word) (dataPorts ins) → Env (ins.map valueWidth)
  | [], .nil => .nil
  | _ :: _, .cons x rest => .cons (valueBits x) (encodeValues rest)

abbrev OpcodeMap (Source : Diamond.Signature Width) (Target : OpSignature) :=
  ∀ {ins out}, Source ins out → Target (ins.map valueWidth) (valueWidth out)

/-- Emit the producer table as typed bindings before a scoped terminator. -/
def lowerCode {Source : Diamond.Signature Width} {Target : OpSignature} {Term : List Width → Type}
    (opcode : OpcodeMap Source Target) : {past sigs : List (List (Diamond.Ty Width))} →
    {Γ : List Width} → (flow : Dataflow Source args past sigs) → Scope args past Γ →
    (∀ {Δ}, Scope args (extend past sigs) Δ → Term Δ) → Code Target Term Γ
  | _, _, _, .nil, scope, finish => .terminator (finish scope)
  | _, _, _, .cons (out := s) op wires rest, scope, finish =>
    .letOp (opcode op) (operands scope wires) (lowerCode opcode rest (scope.pushValue s) finish)

def emit (scope : Scope args past Γ) {ins : List (Diamond.ValueSort Width)}
    {w : Width} (op : Op ins (.data w))
    (wires : Wires args past (dataPorts ins)) : Rhs Γ w :=
  match op, wires with
  | .constant value, .nil => .constant value
  | .binary op, .cons x (.cons y .nil) => .binary op (scope.resolve x) (scope.resolve y)

def lowerFrom {w : Width} : {past sigs : List (List (Diamond.Ty Width))} → {Γ : List Width} →
    (flow : Dataflow Op args past sigs) → Scope args past Γ →
    Origin args (extend past sigs) (.value (.data w)) → Block Γ w
  | _, _, _, .nil, scope, result => .yield (scope.resolve result)
  | _, _, _, .cons (.constant (w := v) value) wires rest, scope, result =>
      .letOp (emit scope (.constant value) wires) (lowerFrom rest (scope.push v) result)
  | _, _, _, .cons (.binary (w := v) op) wires rest, scope, result =>
      .letOp (emit scope (.binary op) wires) (lowerFrom rest (scope.push v) result)

end Lowering

/-- Lower the pure producers of a Sea of Nodes data table to a straight-line
Arith block. The caller selects one word-valued input or producer as the result. -/
def lower {Γ : List Width} {sigs : List (List (Diamond.Ty Width))} {w : Width}
    (flow : Dataflow Op (inputPorts Γ) [] sigs)
    (result : Origin (inputPorts Γ) (extend [] sigs) (.value (.data w))) : Block Γ w :=
  Lowering.lowerFrom flow ⟨Lowering.inputNames Γ, PUnit.unit⟩ result

end Silmaril.SSA.SeaOfNodes.MLIR
