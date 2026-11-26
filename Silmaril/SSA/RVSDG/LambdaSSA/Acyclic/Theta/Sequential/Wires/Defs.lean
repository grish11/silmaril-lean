module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Defs

/-! # Two numbered θ vertices linked by a single live runtime wire -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires

open Isotope.LambdaSSA (Region)
open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Data Threaded runtime runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier Pure)
open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open LinearChain.Wiring (newest)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D : τ}

abbrev First (A M : τ) := Carrier A M M
abbrev Second (M E D : τ) := Carrier M E D

/-- Loop opcodes and structural routing on a single live token. -/
inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | loop {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} : ExplicitRuntime.Effect Φ ins outs → Effect Φ ins outs
  | nested {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} : NestedFeedback.Effect Φ ins outs → Effect Φ ins outs
  | enterNested {A M : τ} : Effect Φ (carried (First A M)) (carried (NestedFeedback.Carrier A M))
  | exitNested {A M : τ} : Effect Φ (carried (NestedFeedback.Carrier A M)) (carried (First A M))
  /-- Enter the consumer from either producer exit of the same payload sort. -/
  | link {A M E D : τ} : Effect Φ (carried (First A M)) (carried (Second M E D))
  /-- Classify completed producer exits into a bypass result or a consumer entry. -/
  | routeExit {H E M D : τ} :
      Effect Φ (carried (Carrier H E M)) (OrderedTheta.results (Carrier M E D))

abbrev Op (Φ : Type u) [HasTy Φ τ] := OrderedRuntime.Structured.Opcode (Pure τ) (Effect Φ)

def liftInstruction {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} :
    OrderedRuntime.Structured.Instruction (Pure τ) (ExplicitRuntime.Effect Φ) ins outs →
      OrderedRuntime.Structured.Instruction (Pure τ) (Effect Φ) ins outs
  | .pure p => .pure p
  | .effect e => .effect (.loop e)

variable {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev Code (Φ : Type u) [HasTy Φ τ] (a : Data args) (b : Data outs)
    (live : Origin (Threaded args) past runtime) (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Σ t : NestedTheta.Term (Op Φ) (Threaded args) past sigs (Threaded outs), Checked (Pure τ) (Effect Φ) a b live t

/-- Reuse admission of the existing θ bodies. Only the instruction signature
embedding changes, so all vertex numbers and token edges are retained. -/
def liftChecked :
    {args outs : Ports (OrderedRuntime.Structured.Ty τ)} → {a : Data args} → {b : Data outs} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} → {live : Origin (Threaded args) past runtime} →
    {t : NestedTheta.Term (ExplicitRuntime.Op Φ) (Threaded args) past sigs (Threaded outs)} →
    Checked (Pure τ) (ExplicitRuntime.Effect Φ) a b live t → Code Φ a b live sigs
  | _, _, _, _, _, _, _, _, .ret live values => ⟨_, .ret live values⟩
  | _, _, _, _, _, _, _, _, .primitive live i o op values rest =>
    ⟨_, .primitive live i o (liftInstruction op) values (liftChecked rest).2⟩
  | _, _, _, _, _, _, _, _, .gamma extra choice live i o values sigs arms rest =>
    ⟨_, .gamma extra choice live i o values sigs (children := fun j => (liftChecked (arms j)).1)
      (fun j => (liftChecked (arms j)).2) (liftChecked rest).2⟩
  | _, _, _, _, _, _, _, _, .theta live i values sigs body rest =>
    ⟨_, .theta live i values sigs (children := fun j => (liftChecked (body j)).1)
      (fun j => (liftChecked (body j)).2) (liftChecked rest).2⟩

abbrev FirstPorts (A M : τ) := carried (First A M)
abbrev SecondPorts (M E D : τ) := carried (Second M E D)
abbrev Signatures (A M E D : τ) :=
  [Threaded (FirstPorts A M), Threaded (SecondPorts M E D), Threaded (SecondPorts M E D)]

def code (s : Loops Φ A B K M C J E D) :
    Code (past := []) Φ (carriedData (First A M)) (carriedData (Second M E D))
      (.arg (runtimePort (FirstPorts A M))) (Signatures A M E D) :=
  let first := ExplicitRuntime.Wiring.thetaBody s.first
  let second := ExplicitRuntime.Wiring.thetaBody s.second
  let firstPorts := FirstPorts A M
  let secondPorts := SecondPorts M E D
  let firstDone := [Threaded firstPorts]
  let linked := firstDone ++ [Threaded secondPorts]
  ⟨_, .theta (.arg (runtimePort firstPorts)) (carriedData _) (.cons (.arg .head) .nil) first.1
    (children := fun _ => (liftChecked first.2.2).1) (fun _ => (liftChecked first.2.2).2) <|
    .primitive (nextRuntime [] firstPorts) (carriedData _) (carriedData _) (.effect .link)
      (.cons (newest .head []) .nil) <|
      .theta (nextRuntime firstDone secondPorts) (carriedData _) (.cons (newest .head firstDone) .nil) second.1
        (children := fun _ => (liftChecked second.2.2).1) (fun _ => (liftChecked second.2.2).2) <|
        .ret (nextRuntime linked secondPorts) (.cons (newest .head linked) .nil)⟩

abbrev Graph (Φ : Type u) [HasTy Φ τ] (A M E D : τ) :=
  NestedTheta.Graph (Op Φ) (Threaded (FirstPorts A M)) [] (Signatures A M E D) (Threaded (SecondPorts M E D))

def graph (s : Loops Φ A B K M C J E D) : Graph Φ A M E D :=
  (code s).1.toGraph

def graphChecked (s : Loops Φ A B K M C J E D) :
    EntryChecked (a := carriedData (First A M)) (b := carriedData (Second M E D)) (graph s).toTerm :=
  (code s).2.collect

inductive Source (A B K M C J E D : τ) : Region Φ → Type u where
  | loops (s : Loops Φ A B K M C J E D) : Source A B K M C J E D (region s)

inductive Related (A B K M C J E D : τ) : Region Φ → Graph Φ A M E D → Type u where
  | loops (s : Loops Φ A B K M C J E D) : Related A B K M C J E D (region s) (graph s)

def lower {r : Region Φ} (w : Source A B K M C J E D r) :
    Σ g : Graph Φ A M E D, Related A B K M C J E D r g :=
  match w with | .loops s => ⟨graph s, .loops s⟩

theorem Related.typing {r : Region Φ} {g : Graph Φ A M E D}
    (w : Related A B K M C J E D r g) : Region.HasType [A] r [E,D] :=
  match w with | .loops s => regionTyping s

def Related.checked {r : Region Φ} {g : Graph Φ A M E D} (w : Related A B K M C J E D r g) :
    EntryChecked (a := carriedData (First A M)) (b := carriedData (Second M E D)) g.toTerm :=
  match w with | .loops s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires
