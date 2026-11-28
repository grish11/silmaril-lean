module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.MLIR.SCF.While.Defs

/-! # Checked PEG loop schedules as native scalar MLIR while regions -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR

open Silmaril.MLIR.Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands i1)
open Silmaril.MLIR.SCF (While)
open RVSDG (Port Tuple)
open Simple.Revert.While.Region (Schedule)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars ins outs : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1} {Γ : List Width}

/-- A width for each source data sort and for count-valued operands.
PEG Boolean values use the native SCF `i1` test type. -/
structure Profile (Data : Type) where
  dataWidth : Data → Width
  countWidth : Width

variable (profile : Profile Data)

def Profile.width : Ty Data → Width
  | .data t => profile.dataWidth t
  | .count => profile.countWidth
  | .bool => i1

abbrev Profile.widths (ts : List (Ty Data)) : List Width := ts.map profile.width
abbrev Profile.carrier (t : Data) : Type := BitVec (profile.dataWidth t).val

def Profile.encodeValue : (t : Ty Data) → t.Value profile.carrier → BitVec (profile.width t).val
  | .data _, value => value
  | .count, value => BitVec.ofNat profile.countWidth.val value.down
  | .bool, value => BitVec.ofBool value.down

def Profile.decodeValue : (t : Ty Data) → BitVec (profile.width t).val → t.Value profile.carrier
  | .data _, value => value
  | .count, value => ⟨value.toNat⟩
  | .bool, value => ⟨value.getLsbD 0⟩

def Profile.encode : {ts : List (Ty Data)} → Tuple (Ty.Value profile.carrier) ts → Env (profile.widths ts)
  | _, .nil => .nil
  | _, .cons x xs => .cons (profile.encodeValue _ x) (encode xs)

def Profile.decode : (ts : List (Ty Data)) → Env (profile.widths ts) → Tuple (Ty.Value profile.carrier) ts
  | [], .nil => .nil
  | _ :: ts, .cons x xs => .cons (profile.decodeValue _ x) (decode ts xs)

/-- Each target symbol is an ordinary single-result primitive with the
ordered operand and result widths of its source opcode. -/
inductive Opcode (P : InstructionSet.{0,0} Data) : Silmaril.MLIR.Pure.OpSignature where
  | apply {ins out} (op : P ins out) : Opcode P (profile.widths ins) (profile.width out)

/-- Interpret PEG primitives by the same MLIR operations at the selected
widths. Count-valued results are decoded as unsigned naturals. -/
def model (evalOp : Eval (Opcode profile P)) : TotalModel P where
  carrier := profile.carrier
  run {_ out} op args := profile.decodeValue out (evalOp (.apply op) (profile.encode args))

namespace Compiler

abbrev Layout (vars : List (Ty Data)) (Γ : List Width) :=
  ∀ {t}, Port vars t → Var Γ (profile.width t)

def Layout.initial : {vars : List (Ty Data)} → Layout profile vars (profile.widths vars)
  | _, _, .head => .here
  | _, _, .tail p => .there (initial p)

/-- Project from the argument prefix, leaving the parent capture suffix unused. -/
def Layout.front : {vars : List (Ty Data)} → Layout profile vars (profile.widths vars ++ Γ)
  | _, _, .head => .here
  | _, _, .tail p => .there (front p)

def Layout.push (layout : Layout profile vars Γ) :
    Layout profile (t :: vars) (profile.width t :: Γ)
  | _, .head => .here
  | _, .tail p => .there (layout p)

def Layout.select (layout : Layout profile vars Γ) (slots : Tuple (Port vars) outs) :
    Layout profile outs Γ :=
  fun p => layout (slots.get p)

def Layout.operands (layout : Layout profile vars Γ) :
    {ins : List (Ty Data)} → Tuple (Port vars) ins → Operands Γ (profile.widths ins)
  | _, .nil => .nil
  | _, .cons p ps => .cons (layout p) (operands layout ps)

def Layout.packet (layout : Layout profile vars Γ) : Operands Γ (profile.widths vars) :=
  Layout.operands profile layout (Simple.ports vars)

/-- Emit one native MLIR SSA binding per checked producer. Earlier references
remain live until the ordered terminator operands are projected. -/
def emit {Term : List Width → Type} {roots : Tuple (Ref g.sort) outs} :
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} → Schedule g false roots scope →
    {Γ : List Width} → Layout profile vars Γ →
    (∀ {Δ}, Layout profile outs Δ → Term Δ) → Code (Opcode profile P) Term Γ
  | _, _, .done reads, _, layout, finish => .terminator (finish (Layout.select profile layout reads.slots))
  | _, _, .bind _ op _ _ _ reads tail, _, layout, finish =>
    .letOp (.apply op) (Layout.operands profile layout reads.slots)
      (emit tail (Layout.push profile layout) finish)
  | _, _, .branch enabled .., _, _, _ => nomatch enabled

end Compiler

/-- Use a single `scf.while`. The guard forwards the old packet, the after
region yields the simultaneous update, and the continuation returns the
stopping packet. All three regions read block arguments in carried order. -/
def lower {g : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
    (b : Bundle g slot invariants) : While (Opcode profile P) (profile.widths carried) (profile.widths carried) where
  State := profile.widths carried
  Payload := profile.widths carried
  init := Compiler.Layout.packet profile (Compiler.Layout.initial profile)
  before := Compiler.emit profile b.scalar.guard (Compiler.Layout.front profile)
    (fun outputs => .condition (outputs .head) (Compiler.Layout.packet profile (fun p => outputs (.tail p))))
  after := Compiler.emit profile b.scalar.update (Compiler.Layout.front profile)
    (fun outputs => .yield (Compiler.Layout.packet profile outputs))
  cont := .terminator (.ret (Compiler.Layout.packet profile (Compiler.Layout.front profile)))

end Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR
