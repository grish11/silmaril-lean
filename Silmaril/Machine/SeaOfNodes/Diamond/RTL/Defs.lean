module

public import Silmaril.Machine.RTL.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.Defs

/-! # Machine RTL for the source-native word diamond

The admitted source graph has two word arguments, one Boolean predicate and
one word-valued Phi return. All data producers belong to the total `WordOp`
signature. The output is one machine RTL.SSA function with four forward blocks.
-/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Diamond.RTL

open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Graph Model Projection Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Origin Port PortType Tuple Wires extend)
open Silmaril.Machine.Lir (Word ofBool)
open Silmaril.Machine.RTL.SSA (Block Func Label Op Prog)

abbrev PortTy := Silmaril.SSA.SeaOfNodes.Diamond.Ty Unit

abbrev word : ValueSort Unit := .data ()
abbrev inputs : List (ValueSort Unit) := [word, word]
abbrev args : List PortTy := dataPorts inputs

/-- The source profile uses wrapping word arithmetic and Boolean comparisons. -/
inductive WordOp : Silmaril.SSA.SeaOfNodes.Diamond.Signature Unit where
  | const (value : Word) : WordOp [] word
  | add : WordOp [word, word] word
  | sub : WordOp [word, word] word
  | eq : WordOp [word, word] .predicate
  | ne : WordOp [word, word] .predicate
  | slt : WordOp [word, word] .predicate

abbrev values : Unit → Type := fun _ => Word

def model : Model WordOp where
  value := values
  run
    | .const value, .nil => value
    | .add, .cons x (.cons y .nil) => BitVec.add x y
    | .sub, .cons x (.cons y .nil) => BitVec.sub x y
    | .eq, .cons x (.cons y .nil) => ⟨BEq.beq (α := Word) x y⟩
    | .ne, .cons x (.cons y .nil) => ⟨!(BEq.beq (α := Word) x y)⟩
    | .slt, .cons x (.cons y .nil) => ⟨decide (x.toInt < y.toInt)⟩

/-- The frame stores numeric predicates as the existing RTL comparison does.
This encoding also types the register invariant for ordered producer tables. -/
def encodeValue : (t : PortTy) → Val model.value t → Word
  | .value .predicate, b => ofBool b.down
  | .value (.data _), w => w
  | .control _, n => BitVec.ofNat 64 n.down.val
  | .state e, _ => nomatch e

def entry (x y : Word) : Tuple (Val model.value) args := .cons x (.cons y .nil)

abbrev WordDiamond (sigs : List (List PortTy)) := Graph WordOp inputs sigs word

/-- Machine register names distinguish function arguments, producer results
and the parameter that receives a Phi operand. Producer numbers are the
source's absolute indices. -/
inductive Reg where
  | arg (index : Nat)
  | node (index : Nat)
  | phi
  deriving DecidableEq, Repr

def portIndex {ts : List PortTy} {t : PortTy} : Port ts t → Nat
  | .head => 0
  | .tail p => portIndex p + 1

/-- Resolve typed arguments in their block context and keep producer indices. -/
def registerWithResults {ports : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (argReg : {ty : PortTy} → Port ports ty → Reg) (resultReg : Nat → Reg) : Origin ports past t → Reg
  | .arg p => argReg p
  | .output i _ => resultReg i.val

def registerWith {ports : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (argReg : {ty : PortTy} → Port ports ty → Reg) (wire : Origin ports past t) : Reg :=
  registerWithResults argReg Reg.node wire

def register {past : List (List PortTy)} {t : PortTy} (wire : Origin args past t) : Reg :=
  registerWith (fun p => .arg (portIndex p)) wire

def emitOpWithResults {ports : List PortTy} {sorts : List (ValueSort Unit)} {out : ValueSort Unit}
    {past : List (List PortTy)} (argReg : {ty : PortTy} → Port ports ty → Reg) (resultReg : Nat → Reg) (dest : Reg) :
    WordOp sorts out → Wires ports past (dataPorts sorts) → Op Reg
  | .const value, _ => .const dest value
  | .add, wires =>
      .binary .add dest (registerWithResults argReg resultReg (wires.get .head))
        (registerWithResults argReg resultReg (wires.get (.tail .head)))
  | .sub, wires =>
      .binary .sub dest (registerWithResults argReg resultReg (wires.get .head))
        (registerWithResults argReg resultReg (wires.get (.tail .head)))
  | .eq, wires =>
      .binary (.cmp .eq) dest (registerWithResults argReg resultReg (wires.get .head))
        (registerWithResults argReg resultReg (wires.get (.tail .head)))
  | .ne, wires =>
      .binary (.cmp .ne) dest (registerWithResults argReg resultReg (wires.get .head))
        (registerWithResults argReg resultReg (wires.get (.tail .head)))
  | .slt, wires =>
      .binary (.cmp .lts) dest (registerWithResults argReg resultReg (wires.get .head))
        (registerWithResults argReg resultReg (wires.get (.tail .head)))

def emitOpWith {ports : List PortTy} {sorts : List (ValueSort Unit)} {out : ValueSort Unit}
    {past : List (List PortTy)} (argReg : {ty : PortTy} → Port ports ty → Reg) (dest : Reg)
    (op : WordOp sorts out) (wires : Wires ports past (dataPorts sorts)) : Op Reg :=
  emitOpWithResults argReg Reg.node dest op wires

def emitOp {sorts : List (ValueSort Unit)} {out : ValueSort Unit}
    {past : List (List PortTy)} (dest : Reg)
    (op : WordOp sorts out) (wires : Wires args past (dataPorts sorts)) : Op Reg :=
  emitOpWith (fun p => .arg (portIndex p)) dest op wires

/-- Emit every source producer in order using the block's argument registers. -/
def emitOpsWith {ports : List PortTy} (argReg : {ty : PortTy} → Port ports ty → Reg) :
    {past sigs : List (List PortTy)} → Dataflow WordOp ports past sigs → List (Op Reg)
  | _, _, .nil => []
  | past, _, .cons op wires rest =>
      emitOpWith argReg (.node past.length) op wires :: emitOpsWith argReg rest

/-- Emit the ordered table in a separate result register range. -/
def emitOpsWithResults {ports : List PortTy} (argReg : {ty : PortTy} → Port ports ty → Reg)
    (resultReg : Nat → Reg) :
    {past sigs : List (List PortTy)} → Dataflow WordOp ports past sigs → List (Op Reg)
  | _, _, .nil => []
  | past, _, .cons op wires rest =>
    emitOpWithResults argReg resultReg (resultReg past.length) op wires :: emitOpsWithResults argReg resultReg rest

/-- Emit each source producer once into the entry block. -/
def emitOps {past sigs : List (List PortTy)} (flow : Dataflow WordOp args past sigs) : List (Op Reg) :=
  emitOpsWith (fun p => .arg (portIndex p)) flow

def armLabel : Projection → Label
  | .onTrue => 1
  | .onFalse => 2

variable {sigs : List (List PortTy)}

def incoming (g : WordDiamond sigs) (p : Projection) : Reg :=
  register (g.phi.operand (g.phi.merge.slot p))

def entryBlock (g : WordDiamond sigs) : Block Reg :=
  ⟨[.arg 0, .arg 1], emitOps g.dataflow,
    .cond (register g.predicate) (armLabel .onTrue) [] (armLabel .onFalse) []⟩

def armBlock (g : WordDiamond sigs) (p : Projection) : Block Reg :=
  ⟨[], [], .jump 3 [incoming g p]⟩

def joinBlock : Block Reg := ⟨[.phi], [], .ret [.phi]⟩

/-- Entry dispatches to two distinct predecessor blocks. Each edge supplies its
own Phi operand to the same join parameter, which is returned by block 3. -/
def lowerFunc (g : WordDiamond sigs) : Func Reg :=
  ⟨⟨2, 1⟩, 0, [entryBlock g, armBlock g .onTrue, armBlock g .onFalse, joinBlock]⟩

def lower (g : WordDiamond sigs) : Prog Reg := ⟨[lowerFunc g]⟩

end Silmaril.Machine.SeaOfNodes.Diamond.RTL
