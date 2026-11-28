module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Defs

/-! # Lower primitive-only checked slices to λSSA bindings -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

open RVSDG (Port Tuple)
open RVSDG.LambdaSSA.Theta
open Isotope (Value)
open Isotope.LambdaSSA (Tm Region)
open Isotope.LambdaSSA.Semantics (Env)

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars outs ins : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1}

abbrev Code (Data : Type) := Silmaril.Ty (ValuePort Data)
abbrev Packet (ts : List (Ty Data)) := Operational.Packed (valuePorts ts)

/-- One PEG primitive retains its original typed operand profile. The test
converts a Boolean atom to the native λSSA case discriminator. -/
inductive Primitive (P : InstructionSet.{0,0} Data) where
  | call {ins out} (op : P ins out)
  | test

def Primitive.inputs : Primitive P → List (Ty Data)
  | .call (ins := ins) _ => ins
  | .test => [.bool]

instance : HasTy (Primitive P) (Code Data) where
  src op := Packet op.inputs
  trg
    | .call (out := out) _ => .base (.value out)
    | .test => .coprod .unit .unit

abbrev Atom (m : TotalModel P) := Operational.Atom (Region.model m)

abbrev pack (m : TotalModel P) (values : Tuple m.toPEG.Value vars) : Value (Atom m) :=
  Operational.pack (Region.model m) (Region.encode m values)

def Primitive.eval (m : TotalModel P) : (op : Primitive P) →
    Tuple m.toPEG.Value op.inputs → Value (Atom m)
  | .call (out := out) op, args => .atom ⟨.value out, m.run op args⟩
  | .test, .cons flag .nil => if flag.down then .inr .unit else .inl .unit

/-- Only one source primitive is executed at a binding. Neither that call
nor the administrative Boolean test changes the ambient state. -/
def instruction (m : TotalModel P) {σ : Type u} (op : Primitive P)
    (arg : Value (Atom m)) (start : σ) (result : Value (Atom m)) (finish : σ) : Prop :=
  ∃ args : Tuple m.toPEG.Value op.inputs,
    arg = pack m args ∧ result = op.eval m args ∧ finish = start

namespace Schedule

open Simple.Revert.While.Region (Schedule)

abbrev Layout (P : InstructionSet.{0,0} Data) (vars : List (Ty Data)) :=
  ∀ {t}, Port vars t → Tm (Primitive P)

def Layout.Typed (layout : Layout P vars) (context : List (Code Data)) : Prop :=
  ∀ t (p : Port vars t), (layout p).HasType context (.base (.value t))

def Layout.Evaluates (layout : Layout P vars) (m : TotalModel P) {σ : Type u}
    (env : Env (Atom m)) (store : Tuple m.toPEG.Value vars) (state : σ) : Prop :=
  ∀ t (p : Port vars t), Isotope.LambdaSSA.Semantics.Tm.Eval
    (instruction m) env (layout p) state (.atom ⟨.value t, store.get p⟩) state

def Layout.shift (layout : Layout P vars) : Layout P vars :=
  fun p => (layout p).rename Nat.succ

def Layout.push (layout : Layout P vars) : Layout P (t :: vars)
  | _, .head => .var 0
  | _, .tail p => layout.shift p

def Layout.select (layout : Layout P vars) (slots : Tuple (Port vars) outs) : Layout P outs :=
  fun p => layout (slots.get p)

/-- Read an old slot using only native product elimination. -/
def field : {vars : List (Ty Data)} → Port vars t → Tm (Primitive P) → Tm (Primitive P)
  | _, .head, packet => .let₂ packet (.var 1)
  | _, .tail p, packet => .let₂ packet (field p (.var 0))

def tupleTerm (layout : Layout P vars) : {ins : List (Ty Data)} →
    Tuple (Port vars) ins → Tm (Primitive P)
  | _, .nil => .unit
  | _, .cons p ps => .pair (layout p) (tupleTerm layout ps)

/-- Each checked producer creates one λSSA let. All earlier slot terms
are shifted under that binder, preserving their references. -/
def emit {roots : Tuple (Ref g.sort) outs} :
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} →
    Schedule g false roots scope → Layout P vars →
    (Layout P outs → Region (Primitive P)) → Region (Primitive P)
  | _, _, .done reads, layout, finish => finish (layout.select reads.slots)
  | _, _, .bind _ op _ _ _ reads tail, layout, finish =>
    .let₁ (.op (.call op) (tupleTerm layout reads.slots)) (emit tail layout.push finish)
  | _, _, .branch enabled _ _ _ _ _ _ _ _ _ _ _, _, _ => nomatch enabled

end Schedule

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA
