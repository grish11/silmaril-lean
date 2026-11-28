module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs

/-! # Composition of mixed structured components at a typed exit -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed

open Isotope.LambdaSSA (Region)
open NestedTheta.ExplicitRuntime (EntryChecked)
open Numbered.Recognize (opcodeCode)
open Recognize (Output)
open StructuredCFG.WithNestedFeedback.Reverse.Recursive (Normal Layout scan weight)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H E M D L : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The producer can have its own input and output carriers. Its first
exit bypasses the consumer and its second enters the consumer's scope.
Either component can itself be a routed link. -/
inductive Component (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | mixed {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Normal Φ A X Z L E D sigs → Component Φ A X Z L E D sigs
  | link {A X Z H E M D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Component Φ A X Z H E M ps → Component Φ M E D M E D qs →
      Component Φ A X Z M E D (ps ++ Selection M E D)

/-- The local bodies at mixed leaves use the canonical instruction association. -/
def Component.Supported : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Component Φ A X Z L E D sigs → Prop
  | _, _, _, _, _, _, _, .mixed n => n.Supported
  | _, _, _, _, _, _, _, .link p q => p.Supported ∧ q.Supported

def Component.source : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Component Φ A X Z L E D sigs → Fragment Φ A E D
  | _, _, _, _, _, _, _, .mixed n => n.toSyntax.source
  | _, _, _, _, _, _, _, .link p q => Flat.linkBy p.source q.source routing

def Component.code : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Component Φ A X Z L E D sigs → Code Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .mixed n => n.toSyntax.code
  | _, _, _, _, _, _, _, .link p q => splice p.code q.code

def Component.graph (s : Component Φ A X Z L E D sigs) : Graph Φ A X Z L E D sigs :=
  s.code.1.toGraph

def Component.checked (s : Component Φ A X Z L E D sigs) :
    EntryChecked (a := payloadData A X Z) (b := payloadData L E D) s.graph.toTerm :=
  s.code.2.collect

/-- The last outer route marks the cut. The consumer is local to its
selected γ child, and the leading labels form the producer's scope. -/
structure CutLayout (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  carry : τ
  bypass : τ
  handoff : τ
  result : τ
  producer : Layout τ Φ
  consumer : Layout τ Φ

def splitLayout (labels : Layout τ Φ) : Option (CutLayout τ Φ) :=
  match labels.reverse with
  | .fork [] consumer :: .route h e m d :: producer =>
    some ⟨h, e, m, d, producer.reverse, consumer⟩
  | _ => none

abbrev Parsed (Φ : Type u) [HasTy Φ τ] (A X Z : τ) :=
  Σ out : Output τ, Component Φ A X Z out.carry out.left out.right out.sigs

def pack (s : Component Φ A X Z L E D sigs) : Parsed Φ A X Z := ⟨⟨L,E,D,sigs⟩, s⟩

def expect [DecidableEq τ] (parsed : Parsed Φ A X Z) (carry e d : τ) :
    Option (Σ sigs, Component Φ A X Z carry e d sigs) :=
  let ⟨out, s⟩ := parsed
  if hc : out.carry = carry then
    if he : out.left = e then
      if hd : out.right = d then some ⟨out.sigs, hc ▸ he ▸ hd ▸ s⟩ else none
    else none
  else none

/-- Follow the canonical route cuts or delegate a leaf to the mixed parser.
Recursion uses only the producer prefix and the selected child. -/
def parse [DecidableEq τ] : Nat → (A X Z : τ) → Layout τ Φ → Option (Parsed Φ A X Z)
  | 0, _, _, _, _ => none
  | fuel + 1, A, X, Z, labels =>
    match splitLayout labels with
    | none => do
      let ⟨out, n⟩ ← StructuredCFG.WithNestedFeedback.Reverse.Recursive.parse (weight labels) A X Z labels
      return ⟨out, .mixed n⟩
    | some ⟨h,e,m,d,producer,consumer⟩ => do
      let ⟨_, p⟩ ← expect (← parse fuel A X Z producer) h e m
      let ⟨_, q⟩ ← expect (← parse fuel m e d consumer) m e d
      return pack (.link p q)

def decodeLayout [DecidableEq τ] (labels : Layout τ Φ) : Option (Component Φ A X Z L E D sigs) := do
  let ⟨out, component⟩ ← parse (weight labels + 1) A X Z labels
  if eq : out = (⟨L,E,D,sigs⟩ : Output τ) then
    some (Eq.mp (congrArg (fun ix => Component Φ A X Z ix.carry ix.left ix.right ix.sigs) eq) component)
  else none

def candidate [DecidableEq τ] (g : Graph Φ A X Z L E D sigs) : Option (Component Φ A X Z L E D sigs) :=
  (scan g.toTerm).bind decodeLayout

inductive Related (g : Graph Φ A X Z L E D sigs) : Region Φ → Type u where
  | generated (s : Component Φ A X Z L E D sigs) (wiring : s.graph = g) : Related g s.source.region

abbrev Fibre (g : Graph Φ A X Z L E D sigs) :=
  Σ r : Region Φ, Related g r

/-- Reuse a certified component at another cut. Its numbered graph and
flat region are the ones supplied to the relation. -/
def Related.component {g : Graph Φ A X Z L E D sigs} {r : Region Φ} (w : Related g r) :
    {s : Component Φ A X Z L E D sigs // s.graph = g ∧ s.source.region = r} :=
  match w with | .generated s wiring => ⟨s, wiring, rfl⟩

theorem Related.typing {g : Graph Φ A X Z L E D sigs} {r : Region Φ} (w : Related g r) :
    Region.HasType [A] r [E,D] :=
  match w with | .generated s _ => s.source.typing

/-- Certify the entire re-emission, including every cut, child scope,
capture and routed token. -/
def certify [DecidableEq τ] [DecidableEq Φ] (g : Graph Φ A X Z L E D sigs)
    (s : Component Φ A X Z L E D sigs) : Option (Fibre g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) s.graph g
  if wiring : s.graph = g then some ⟨s.source.region, .generated s wiring⟩ else none

def recover [DecidableEq τ] [DecidableEq Φ] (g : Graph Φ A X Z L E D sigs) : Option (Fibre g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed
