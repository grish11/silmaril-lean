module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Defs

/-! # Heterogeneous producer exits with a checked numbered γ handoff -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed

open Isotope.LambdaSSA (Region)
open OrderedTheta (carried carriedData results resultData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier)
open NestedTheta.ExplicitRuntime (EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (append)
open LinearChain.Wiring (newest)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y H B K M C J E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The first exit is external; the second starts the consumer with its own payload sort. -/
def routing : ExitRouting E M M E D := ⟨.first, .consumer⟩

abbrev Selection (M E D : τ) :=
  [Threaded (results (Carrier M E D)), WirePorts M E D]

/-- After decoding the producer's exit carrier, γ passes the output token
to the bypass or consumer. The bypass is an empty region. -/
def select (q : Code Φ M E D M E D qs) :
    Code Φ H E M M E D (Selection M E D) :=
  let classified := results (Carrier M E D)
  let joined := carried (Carrier M E D)
  let before := [Threaded classified]
  let arms j := Fin.cases (motive := fun (_ : Fin 2) => Σ sigs, Code Φ M E D M E D sigs)
    ⟨[], ⟨_, .ret (.arg (runtimePort joined)) (.cons (.arg .head) .nil)⟩⟩
    (fun _ => ⟨qs, q⟩) j
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier H E M)))) (carriedData _) (resultData _)
    (.effect .routeExit) (.cons (.arg .head) .nil) <|
      .gamma 0 (newest .head []) (nextRuntime [] classified) (carriedData (Carrier M E D))
        (carriedData (Carrier M E D)) (.cons (newest (.tail .head) []) .nil) (fun j => (arms j).1)
        (children := fun j => (arms j).2.1) (fun j => (arms j).2.2)
        (.ret (nextRuntime before joined) (.cons (newest .head before) .nil))⟩

def splice (p : Code Φ A X Y H E M ps) (q : Code Φ M E D M E D qs) :
    Code Φ A X Y M E D (ps ++ Selection M E D) :=
  append (select q).2 p.2

/-- The admitted source has a loop on each side of the typed cut. -/
structure Source (Φ : Type u) [HasTy Φ τ] (A B K M C J E D : τ) where
  producer : Loop Φ A B K E M
  consumer : Loop Φ M C J E D

def Source.source (s : Source Φ A B K M C J E D) : Fragment Φ A E D :=
  Flat.linkBy (.loop s.producer) (.loop s.consumer) routing

abbrev Signatures (A E M D : τ) := [WirePorts A E M] ++ Selection M E D

def Source.code (s : Source Φ A B K M C J E D) :
    Code Φ A E M M E D (Signatures A E M D) :=
  splice (Spine.loop s.producer).code (Spine.loop s.consumer).code

def Source.graph (s : Source Φ A B K M C J E D) :
    Graph Φ A E M M E D (Signatures A E M D) :=
  s.code.1.toGraph

inductive Related (A B K M C J E D : τ) :
    Region Φ → Graph Φ A E M M E D (Signatures A E M D) → Type u where
  | generated (s : Source Φ A B K M C J E D) : Related A B K M C J E D s.source.region s.graph

def lower (s : Source Φ A B K M C J E D) :
    Σ g, Related A B K M C J E D s.source.region g :=
  ⟨s.graph, .generated s⟩

theorem Related.typing {r : Region Φ} {g : Graph Φ A E M M E D (Signatures A E M D)}
    (w : Related A B K M C J E D r g) : Region.HasType [A] r [E,D] :=
  match w with | .generated s => s.source.typing

def Related.checked {r : Region Φ} {g : Graph Φ A E M M E D (Signatures A E M D)}
    (w : Related A B K M C J E D r g) :
    EntryChecked (a := payloadData A E M) (b := payloadData M E D) g.toTerm :=
  match w with | .generated s => s.code.2.collect

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed
