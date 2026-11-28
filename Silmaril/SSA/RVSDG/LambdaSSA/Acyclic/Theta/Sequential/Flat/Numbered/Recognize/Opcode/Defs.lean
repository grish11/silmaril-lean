module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Opcode.Defs

/-! # Codes retain generator parameters omitted by the label readers -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

open OrderedRuntime.Structured (Ty Instruction)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

inductive RouteCode (τ : Type u)
  | direct (a : τ)
  | left (l r : τ)
  | right (l r : τ)
  deriving DecidableEq

def routeCode : {S A : τ} → Acyclic.Input S A → RouteCode τ
  | _, _, .direct (A := a) => .direct a
  | _, _, .left (X := x) (Y := y) => .left x y
  | _, _, .right (X := x) (Y := y) => .right x y

inductive OpcodeKey (τ Φ : Type u)
  | exit (a b e d : τ)
  | nested (key : NestedFeedback.Reverse.Key τ Φ)
  | enterNested (a m : τ)
  | exitNested (a m : τ)
  | classifyPayload (a : τ) (op : Φ)
  | enterCarrier (a e d : τ)
  | link (a m e d : τ)
  | routeExit (h e m d : τ)
  | header (a b e d : τ) (op : Φ)
  | join (a k e d : τ) (op : Φ)
  | call (s a b : τ) (route : RouteCode τ) (op : Φ)
  | classify (s a x y : τ) (route : RouteCode τ) (op : Φ)
  deriving DecidableEq

def pureKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    TwoBlock.TwoExit.Pure τ ins outs → OpcodeKey τ Φ
  | _, _, .exit (A := a) (B := b) (C := e) (D := d) => .exit a b e d

def acyclicKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    Acyclic.Opcode Φ ins outs → OpcodeKey τ Φ
  | _, _, .call (S := s) (A := a) (B := b) route p => .call s a b (routeCode route) p.op
  | _, _, .classify (S := s) (A := a) (X := x) (Y := y) route p =>
    .classify s a x y (routeCode route) p.op

def loopKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    ExplicitRuntime.Effect Φ ins outs → OpcodeKey τ Φ
  | _, _, .header (A := a) (B := b) (E := e) (D := d) p => .header a b e d p.op
  | _, _, .join (A := a) (K := k) (E := e) (D := d) p => .join a k e d p.op
  | _, _, .acyclic op => acyclicKey op

def effectKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    Wires.Effect Φ ins outs → OpcodeKey τ Φ
  | _, _, .classifyPayload (A := a) p => .classifyPayload a p.op
  | _, _, .enterCarrier (A := a) (E := e) (D := d) => .enterCarrier a e d
  | _, _, .link (A := a) (M := m) (E := e) (D := d) => .link a m e d
  | _, _, .routeExit (H := h) (E := e) (M := m) (D := d) => .routeExit h e m d
  | _, _, .loop op => loopKey op
  | _, _, .nested op => .nested (NestedFeedback.Reverse.effectKey op)
  | _, _, .enterNested (A := a) (M := m) => .enterNested a m
  | _, _, .exitNested (A := a) (M := m) => .exitNested a m

def instructionKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) ins outs → OpcodeKey τ Φ
  | _, _, .pure op => pureKey op
  | _, _, .effect op => effectKey op

def opcodeKey : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} → Wires.Op Φ ins outs → OpcodeKey τ Φ
  | _, _, .ordered _ _ op => instructionKey op

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
