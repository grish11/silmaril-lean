module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.Defs

/-! # Recover a mixed γ followed by an ordered θ

The left arm has the admitted mixed θ and both arms end in the same
carrier-producing instruction. The shared continuation is a local ordered
loop with an acyclic body. The input graph supplies the selector, the
instruction labels, both child scopes, and the continuation. The final
comparison checks every address, including the γ-to-θ seam.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse

open Sequential
open Flat.Serial (WirePorts)
open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open NestedTheta.ExplicitRuntime.PurePrefix (Code lift)
open NestedTheta.ExplicitRuntime.PurePrefix.Splice (appendOrdered)
open LinearChain.Wiring (newest)
open TwoBlock.TwoExit (Carrier)
open PureGamma (inputData ValueOp)
open StructuredCFG.WithNestedFeedback.Reverse.Recursive (scan readLeaf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A M E D : τ}

/-- The outer positions are a γ and its shared θ continuation. -/
abbrev Graph (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A M E D : τ) :=
  NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (Threaded (PureGamma.Input A)) []
    [WirePorts M E D, WirePorts M E D] (WirePorts M E D)

structure Shape (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A M E D : τ) where
  loop : PureTheta.Loop Φ ε A
  pureFirst : Bool
  bridge : TwoBlock.Instruction Φ A (Carrier M E D)
  bodyType : τ
  joinType : τ
  tail : Loop Φ M bodyType joinType E D

def Shape.fragment (s : Shape Φ ε A M E D) : Flat.Fragment Φ (PureGamma.Choice A) E D :=
  Flat.link s.loop.fragment.splitReturn ((Flat.Fragment.loop s.tail).gateCarrier s.bridge)

def bridgeCode (gate : TwoBlock.Instruction Φ A (Carrier M E D)) :
    Wires.Code (past := []) Φ (carriedData A) (carriedData (Carrier M E D))
      (.arg (runtimePort (carried A))) [WirePorts M E D] :=
  ⟨_, .primitive (.arg (runtimePort (carried A))) (carriedData _) (carriedData _)
    (PurePrefix.orderedCall gate) (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] (carried (Carrier M E D))) (.cons (newest .head []) .nil))⟩

abbrev Arm (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A M E D : τ)
    (rows : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
    (carriedData A) (carriedData (Carrier M E D)) (.arg (runtimePort (carried A))) rows

def Shape.left (s : Shape Φ ε A M E D) : Arm Φ ε A M E D [Threaded (carried A), WirePorts M E D] :=
  appendOrdered (bridgeCode s.bridge).2 (s.loop.compileChecked s.pureFirst)

def Shape.right (s : Shape Φ ε A M E D) : Arm Φ ε A M E D [WirePorts M E D] :=
  lift (bridgeCode s.bridge).2

def Shape.headCode (s : Shape Φ ε A M E D) :
    Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
      (inputData A) (carriedData (Carrier M E D)) (.arg (runtimePort (PureGamma.Input A))) [WirePorts M E D] :=
  let arms : Fin 2 → Σ rows, Arm Φ ε A M E D rows :=
    Fin.cases ⟨_, s.left⟩ (fun _ => ⟨_, s.right⟩)
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort (PureGamma.Input A))) (carriedData A) (carriedData (Carrier M E D))
    (.cons (.arg (.tail .head)) .nil) (fun i => (arms i).1) (children := fun i => (arms i).2.1)
    (fun i => (arms i).2.2)
    (.ret (nextRuntime [] (carried (Carrier M E D))) (.cons (newest .head []) .nil))⟩

def Shape.suffix (s : Shape Φ ε A M E D) :
    Translation.Fibre .mixed (Flat.Serial.Spine.loop s.tail).graph :=
  ⟨(Flat.Fragment.loop s.tail).region, .generated (.structured (.loop s.tail))⟩

def Shape.headChecked (s : Shape Φ ε A M E D) :
    NestedTheta.ExplicitRuntime.PurePrefix.EntryChecked
      (a := inputData A) (b := Flat.Serial.payloadData M E D) s.headCode.1.toGraph.toTerm :=
  (NestedTheta.Term.toTerm_toGraph s.headCode.1).symm ▸ s.headCode.2

def Shape.emit (s : Shape Φ ε A M E D) : Graph Φ ε A M E D :=
  linkRecovered s.headChecked s.suffix

abbrev collectFin : {n : Nat} → {T : Fin n → Type u} →
    ((i : Fin n) → Option (T i)) → Option ((i : Fin n) → T i) :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.collectChildren

/-- Recheck the dialect in place. Whole-graph certification checks the actual
cut and its origins separately. -/
def orderedView {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past rows : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (term : NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) args past rows outs) :
    Option (NestedTheta.Term (Wires.Op Φ) args past rows outs) :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.orderedSuffix
    NestedTheta.ExplicitRuntime.PurePrefix.Splice.Reverse.Routing.identity term

variable [DecidableEq τ]

def readBridge (rows : List (MixedRows.Row τ Φ ε)) :
    Option (TwoBlock.Instruction Φ A (Carrier M E D)) := do
  let [.ordered (.call op)] := rows | none
  MixedRows.instruction A (Carrier M E D) op.op

def readLeft {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {rows : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (term : NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) args [] rows outs) :
    Option ((PureTheta.Loop Φ ε A × Bool) × TwoBlock.Instruction Φ A (Carrier M E D)) :=
  match term with
  | .ret _ => none
  | .bind node children rest => do
    let loop ← PureTheta.Reverse.decode (← PureTheta.Reverse.readTheta node.kind children)
    let bridge ← readBridge (← MixedRows.readScope rest)
    return (loop, bridge)

def readHead : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (PureGamma.Op (τ := τ) Φ ε) ins outs) →
    {sigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (PureGamma.Op (τ := τ) Φ ε) kind.entry [] (sigs j) kind.exit) →
    Option ((PureTheta.Loop Φ ε A × Bool) ×
      TwoBlock.Instruction Φ A (Carrier M E D) × TwoBlock.Instruction Φ A (Carrier M E D))
  | _, _, .base (.gamma 0), _, children => do
    let (loop, bridge) ← readLeft (children (0 : Fin 2))
    let right ← readBridge (← MixedRows.readScope (children (1 : Fin 2)))
    return (loop, bridge, right)
  | _, _, _, _, _ => none

variable [DecidableEq Φ]

/-- Read opcode and scope structure before checking addresses. The ordinary
suffix is parsed in place with the existing recursive leaf parser. -/
def candidate (g : Graph Φ ε A M E D) : Option (Shape Φ ε A M E D) :=
  match g.toTerm with
  | .bind node children rest => do
    let ((loop, order), bridge, right) ← readHead node.kind children
    if bridge.op = right.op then
      let labels ← scan (← orderedView rest)
      let (⟨_, .localLoop tail⟩, []) ← readLeaf (Φ := Φ) M E D labels | none
      return ⟨loop, order, bridge, _, _, tail⟩
    else none

structure Fibre (g : Graph Φ ε A M E D) where
  shape : Shape Φ ε A M E D
  wiring : shape.emit = g

def Fibre.fragment {g : Graph Φ ε A M E D} (f : Fibre g) : Flat.Fragment Φ (PureGamma.Choice A) E D :=
  f.shape.fragment

def certify (g : Graph Φ ε A M E D) (shape : Shape Φ ε A M E D) : Option (Fibre g) :=
  letI := MixedRows.decideGraph shape.emit g
  if eq : shape.emit = g then some ⟨shape, eq⟩ else none

/-- The numbered input supplies both component views. Certify exact
re-emission, including the current γ-result token at the cut. -/
def recover (g : Graph Φ ε A M E D) : Option (Fibre g) :=
  candidate g >>= certify g

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse
