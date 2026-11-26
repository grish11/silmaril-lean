module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs

/-! # A routed producer with a mixed structured consumer -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed

open Isotope.LambdaSSA (Region)
open NestedTheta.ExplicitRuntime (EntryChecked)
open Numbered.Recognize (RightAssociated loop opcodeCode)
open StructuredCFG.WithNestedFeedback.Reverse.Recursive (Normal)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A E M D : τ}
variable {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}

/-- A local producer θ routes its first exit out of the region and its
second into a canonical mixed consumer. The consumer's numbering is local
to the selected γ arm. -/
structure Components (Φ : Type u) [HasTy Φ τ] (A E M D : τ) where
  B : τ
  K : τ
  producer : Loop Φ A B K E M
  rows : List (Ports (OrderedRuntime.Structured.Ty τ))
  consumer : Normal Φ M E D M E D rows

def Components.Supported (s : Components Φ A E M D) : Prop :=
  RightAssociated s.producer.body ∧ s.consumer.Supported

def Components.source (s : Components Φ A E M D) : Fragment Φ A E D :=
  Flat.linkBy (.loop s.producer) s.consumer.toSyntax.source routing

def Components.code (s : Components Φ A E M D) : Code Φ A E M M E D (Signatures A E M D) :=
  splice (Spine.loop s.producer).code s.consumer.toSyntax.code

def Components.graph (s : Components Φ A E M D) : Reverse.CanonicalGraph Φ A E M D :=
  s.code.1.toGraph

def Components.checked (s : Components Φ A E M D) :
    EntryChecked (a := payloadData A E M) (b := payloadData M E D) s.graph.toTerm :=
  s.code.2.collect

abbrev Consumer (Φ : Type u) [HasTy Φ τ] (M E D : τ) :=
  Σ rows, Normal Φ M E D M E D rows

/-- Check the child interface before running the existing mixed parser.
The complete comparison later checks the actual operands of the γ. -/
def readConsumer [DecidableEq τ] {entry exit : Ports (OrderedRuntime.Structured.Ty τ)}
    {rows : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (t : NestedTheta.Term (Wires.Op Φ) entry [] rows exit) : Option (Consumer Φ M E D) := do
  if hEntry : entry = WirePorts M E D then
    if hExit : exit = WirePorts M E D then
      let same := congrArg₂ (fun i o => NestedTheta.Graph (Wires.Op Φ) i [] rows o) hEntry hExit
      let child : Graph Φ M E D M E D rows := Eq.mp same t.toGraph
      let n ← StructuredCFG.WithNestedFeedback.Reverse.Recursive.candidate child
      return ⟨rows, n⟩
    else none
  else none

def readBranch [DecidableEq τ] : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Wires.Op Φ) ins outs) →
    {childSigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Wires.Op Φ) kind.entry [] (childSigs j) kind.exit) →
    Option (Consumer Φ M E D)
  | _, _, .base (.gamma 0), _, arms =>
    if Reverse.emptyTerm (arms (0 : Fin 2)) then readConsumer (arms (1 : Fin 2)) else none
  | _, _, _, _, _ => none

/-- Read the producer loop and the complete selected arm from the input
graph. The outer layout supplies no source syntax or child row count. -/
def candidate [DecidableEq τ] (g : Reverse.CanonicalGraph Φ A E M D) : Option (Components Φ A E M D) :=
  match g.toTerm with
  | .bind producer body (.bind route _ (.bind branch arms (.ret _))) =>
    if Reverse.isRoute route.kind then do
      let (fuel, labels) ← Reverse.readLoop producer.kind body
      let ⟨b, k, p⟩ ← loop fuel A E M labels
      let ⟨rows, q⟩ ← readBranch branch.kind arms
      pure ⟨b, k, p, rows, q⟩
    else none

inductive Related (g : Reverse.CanonicalGraph Φ A E M D) : Region Φ → Type u where
  | generated (s : Components Φ A E M D) (wiring : s.graph = g) : Related g s.source.region

abbrev Fibre (g : Reverse.CanonicalGraph Φ A E M D) :=
  Σ r : Region Φ, Related g r

theorem Related.typing {g : Reverse.CanonicalGraph Φ A E M D} {r : Region Φ} (w : Related g r) :
    Region.HasType [A] r [E,D] :=
  match w with | .generated s _ => s.source.typing

/-- Certify the entire re-emission, including both sides of the routed cut,
all child captures and the token entering the selected arm. -/
def certify [DecidableEq τ] [DecidableEq Φ] (g : Reverse.CanonicalGraph Φ A E M D) (s : Components Φ A E M D) :
    Option (Fibre g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) s.graph g
  if wiring : s.graph = g then some ⟨s.source.region, .generated s wiring⟩ else none

def recover [DecidableEq τ] [DecidableEq Φ] (g : Reverse.CanonicalGraph Φ A E M D) : Option (Fibre g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed
