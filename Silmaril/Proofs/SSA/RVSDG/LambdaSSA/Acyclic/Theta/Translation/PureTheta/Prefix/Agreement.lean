module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point carried carriedData)
open Sequential
open Flat.Serial (WirePorts payloadData)
open PureGamma (model OrderedModel evalValue)
open TwoBlock.TwoExit (enter Carrier)
open OrderedRuntime.Structured (Threaded RuntimeValues)
open NestedTheta.Partial (observe)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private abbrev ValueTuple (ps : Ports (OrderedRuntime.Structured.Ty τ)) :=
  Tuple (RuntimeValues (TyDen (τ := τ)) σ) ps

private theorem adapter_observe (p : ValueTuple (σ := σ) (InputPorts A)) :
    observe (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))
        (adapter Φ A X Z).1.toGraph p =
      Part.some (point (enter (A := A) (C := X) (D := Z) (p.get .head)) (p.get (.tail .head))) := by
  unfold observe
  rw [NestedTheta.Term.toTerm_toGraph]
  cases p with
  | cons x rest =>
    cases rest with
    | cons token rest =>
      cases rest
      change (Part.some (point (enter (A := A) (C := X) (D := Z) x) token)).bind _ = _
      rw [Part.bind_some]
      rfl

theorem enterGraph_observe {raw : NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε)
      (InputPorts A) [] sigs (InputPorts A)}
    (head : NestedTheta.ExplicitRuntime.PurePrefix.EntryChecked
      (a := carriedData A) (b := carriedData A) raw.toTerm)
    (input : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (InputPorts A)) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (enterGraph head X Z) input =
      Part.map (fun p => point (enter (A := A) (C := X) (D := Z) (p.get .head)) (p.get (.tail .head)))
        (observe (model (Φ := Φ) (ε := ε) (σ := σ)) raw input) := by
  unfold enterGraph
  rw [NestedTheta.ExplicitRuntime.PurePrefix.Splice.graph_observe (OrderedModel (ε := ε)) evalValue,
    Part.bind_eq_bind, ← Part.bind_some_eq_map]
  congr 1
  funext p
  exact adapter_observe (Φ := Φ) (ε := ε) p

private theorem producer_observe (s : Loop Φ ε A) (pureFirst : Bool) (x : TyDen A) (token : σ)
    (next : ValueTuple (σ := σ) (WirePorts A X Z) → Part (ValueTuple (σ := σ) (WirePorts L E D))) :
    (observe (model (Φ := Φ) (ε := ε) (σ := σ)) (producer s pureFirst X Z) (point x token)).bind next =
      (observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point x token)).bind
        (fun p => next (point (enter (p.get .head)) (p.get (.tail .head)))) := by
  rw [producer, enterGraph_observe, Part.bind_map]

theorem compile_observe (s : Loop Φ ε A) (pureFirst : Bool)
    (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D sigs) (x : TyDen A) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (compile s pureFirst tail) (point x initial) =
      (observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point x initial)).bind
        (fun p => Flat.Serial.observe (ε := ε) (σ := σ) (Translation.compile (.mixed tail))
          (p.get .head) (p.get (.tail .head))) := by
  rw [compile, MixedContinuation.compile_observe]
  exact producer_observe s pureFirst x initial _

theorem candidate_observe (c : Candidate Φ ε A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) c.emit (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) c.link.fragment.typing env).run initial) := by
  rw [Candidate.emit, linkRecovered, MixedContinuation.linkRecovered_observe]
  exact (producer_observe c.loop c.pureFirst env.2 initial _).trans (c.link.region_observe coherent env initial)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Proofs
