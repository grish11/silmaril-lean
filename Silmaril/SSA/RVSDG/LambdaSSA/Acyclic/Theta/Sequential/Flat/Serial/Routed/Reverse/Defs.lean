module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Check.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms

/-! # Recover a routed flat CFG from a typed numbered γ -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse

open Isotope.LambdaSSA (Region)
open Numbered.Recognize (budget loop opcodeCode)
open Wires.Reverse (Vertex readBody)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {ins out : Ports (OrderedRuntime.Structured.Ty τ)}

abbrev CanonicalGraph (Φ : Type u) [HasTy Φ τ] (A E M D : τ) :=
  Graph Φ A E M M E D (Signatures A E M D)

abbrev LoopLabels (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] := Nat × List (Vertex (τ := τ) (Φ := Φ))

def readLoop (kind : NestedTheta.Kind (Wires.Op Φ) ins out)
    {childSigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))}
    (children : (j : Fin kind.arity) →
      NestedTheta.Term (Wires.Op Φ) kind.entry [] (childSigs j) kind.exit) : Option (LoopLabels τ Φ) :=
  match kind with
  | .theta _ => do
    let body := children (0 : Fin 1)
    return (budget body, [.theta (← readBody body)])
  | _ => none

def effectIsRoute : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} → Wires.Effect Φ ins out → Bool
  | _, _, .routeExit => true
  | _, _, _ => false

def isRoute : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    NestedTheta.Kind (Wires.Op Φ) ins out → Bool
  | _, _, .base (.simple (.ordered _ _ (.effect op))) => effectIsRoute op
  | _, _, _ => false

def emptyTerm {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past : List (Ports (OrderedRuntime.Structured.Ty τ))} :
    {rows : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Wires.Op Φ) args past rows outs → Bool
  | _, .ret _ => true
  | _, .bind .. => false

def readSingleLoop {args outs : Ports (OrderedRuntime.Structured.Ty τ)} :
    {rows : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Wires.Op Φ) args [] rows outs → Option (LoopLabels τ Φ)
  | _, .bind node children (.ret _) => readLoop node.kind children
  | _, _ => none

def readConsumer : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Wires.Op Φ) ins out) →
    {childSigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Wires.Op Φ) kind.entry [] (childSigs j) kind.exit) →
    Option (LoopLabels τ Φ)
  | _, _, .base (.gamma 0), _, children =>
    if emptyTerm (children (0 : Fin 2)) then readSingleLoop (children (1 : Fin 2)) else none
  | _, _, _, _, _ => none

abbrev CanonicalTerm (Φ : Type u) [HasTy Φ τ] (A E M D : τ) :=
  NestedTheta.Term (Wires.Op Φ) (WirePorts A E M) [] (Signatures A E M D) (WirePorts M E D)

/-- Read only the producer θ, route opcode, empty bypass and consumer θ.
The syntax readers leave all addresses to the wiring check. -/
def scan (t : CanonicalTerm Φ A E M D) : Option (LoopLabels τ Φ × LoopLabels τ Φ) :=
  match t with
  | .bind producer body (.bind route _ (.bind branch arms (.ret _))) =>
    if isRoute route.kind then do
      let p ← readLoop producer.kind body
      let q ← readConsumer branch.kind arms
      pure (p, q)
    else none

abbrev Components (Φ : Type u) [HasTy Φ τ] (A E M D : τ) :=
  Σ B K C J : τ, Source Φ A B K M C J E D

def candidate [DecidableEq τ] (g : CanonicalGraph Φ A E M D) : Option (Components Φ A E M D) := do
  let (p, q) ← scan g.toTerm
  let ⟨b, k, producer⟩ ← loop p.1 A E M p.2
  let ⟨c, j, consumer⟩ ← loop q.1 M E D q.2
  pure ⟨b, k, c, j, ⟨producer, consumer⟩⟩

/-- The canonical representative supplies only the graph. The recursive
isomorphism checks labels, child scopes, and operand and result addresses. -/
structure View (actual : Graph Φ A E M M E D sigs) where
  representative : CanonicalGraph Φ A E M D
  numbering : NestedTheta.Graph.Isomorphic (Wires.Op Φ) actual representative

inductive Related (actual : Graph Φ A E M M E D sigs) : Region Φ → Type u where
  | routed {B K C J : τ} (s : Source Φ A B K M C J E D)
      (numbering : NestedTheta.Graph.Isomorphic (Wires.Op Φ) actual s.graph) :
      Related actual s.source.region

abbrev Fibre (actual : Graph Φ A E M M E D sigs) :=
  Σ r : Region Φ, Related actual r

theorem Related.typing {g : Graph Φ A E M M E D sigs} {r : Region Φ} (w : Related g r) :
    Region.HasType [A] r [E,D] :=
  match w with | .routed s _ => s.source.typing

/-- Certify every edge and child by re-emitting the parsed loops at the
representative's numbering. The actual graph uses the supplied correspondence. -/
def certify [DecidableEq τ] [DecidableEq Φ] {g : Graph Φ A E M M E D sigs} (view : View g)
    (parts : Components Φ A E M D) : Option (Fibre g) :=
  let ⟨_, _, _, _, s⟩ := parts
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) s.graph view.representative
  if h : s.graph = view.representative then
    some ⟨s.source.region, .routed s (h.symm ▸ view.numbering)⟩
  else none

/-- Recover an actual flat `linkBy` region. The caller supplies a checked
isomorphism when using a separate representative. -/
def recover [DecidableEq τ] [DecidableEq Φ] {g : Graph Φ A E M M E D sigs} (view : View g) : Option (Fibre g) :=
  (candidate view.representative).bind (certify view)

/-- Run the recognizer directly on a graph at the admitted outer layout. -/
def recognize [DecidableEq τ] [DecidableEq Φ] (g : CanonicalGraph Φ A E M D) : Option (Fibre g) :=
  recover ⟨g, NestedTheta.Graph.Isomorphic.refl g⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse
