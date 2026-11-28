module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Thms

import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open Sequential
open OrderedTheta (point carried carriedData exit)
open OrderedRuntime.Structured (RuntimeValues Threaded)
open NestedTheta.Partial (observe)
open NestedTheta.ExplicitRuntime.PurePrefix (gamma_denote lift_denote)
open NestedTheta.ExplicitRuntime.PurePrefix.Splice (append_denote)
open PureGamma (Choice OrderedModel model evalValue)
open TwoBlock.TwoExit (Carrier ExitCode callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A M E D : τ}

private abbrev Point (X : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried X))

private theorem repack {X : τ} (r : Point (σ := σ) X) : point (r.get .head) (r.get (.tail .head)) = r := by
  cases r with
  | cons v tail =>
    cases tail with
    | cons token tail => cases tail; rfl

private theorem forward {X : τ} (result : Part (Point (σ := σ) X)) :
    result.bind (fun out => Part.some (point (out.get .head) (out.get (.tail .head)))) = result := by
  have ret : (fun out : Point (σ := σ) X => Part.some
      (point (out.get .head) (out.get (.tail .head)))) = Part.some := by
    funext out
    exact congrArg Part.some (repack out)
  rw [ret, Part.bind_some_right]

private theorem bridge_denote (gate : TwoBlock.Instruction Φ A (Carrier M E D)) (x : TyDen A) (token : σ) :
    (bridgeCode gate).1.denoteOpenWith (OrderedModel (ε := ε)) (point x token) PUnit.unit =
      Part.map (fun p => point p.1 p.2) ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) gate x).run token) := by
  change ((OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
    (.ordered (carriedData A) (carriedData (Carrier M E D)) (PurePrefix.orderedCall gate))
    (point x token)).bind _ = _
  rw [PurePrefix.orderedCall_denote, Part.bind_map, ← Part.bind_some_eq_map]
  rfl

private theorem head_observe (s : Shape Φ ε A M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) s.headCode.1.toGraph (PureGamma.entry env.2 initial) =
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.loop.fragment.splitReturn.typing env).run initial).bind
        (fun r => Part.map (fun p => point p.1 p.2) ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u})
          s.bridge (merge r.1)).run r.2)) := by
  rw [Flat.Fragment.splitReturn_denote _ coherent]
  simp only [observe, NestedTheta.Term.toTerm_toGraph, Shape.headCode, gamma_denote, PureGamma.entry]
  cases TypeModel.coprodEquiv A A env.2 with
  | inl x =>
    change ((s.left.1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ)) (point x initial) PUnit.unit).bind
      (fun out => Part.some (point (out.get .head) (out.get (.tail .head))))) = _
    refine (forward (σ := σ) (X := Carrier M E D) _).trans ?_
    simp only [Shape.left, append_denote]
    have observed := s.loop.region_observe s.pureFirst coherent (PUnit.unit, x) initial
    rw [s.loop.region_denote coherent] at observed
    unfold observe at observed
    rw [observed, s.loop.fragment_denote coherent]
    simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_eq_map,
      Part.map_map, Part.bind_map]
    congr 1
    funext r
    exact bridge_denote s.bridge r.1 r.2
  | inr x =>
    change ((s.right.1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ)) (point x initial) PUnit.unit).bind
      (fun out => Part.some (point (out.get .head) (out.get (.tail .head))))) = _
    refine (forward (σ := σ) (X := Carrier M E D) _).trans ?_
    simp only [Shape.right, lift_denote, StateT.run_pure, Part.pure_eq_some, Part.bind_some]
    exact bridge_denote s.bridge x initial

private theorem tail_completed (s : Shape Φ ε A M E D) (label : TyDen E ⊕ TyDen D) (token : σ) :
    observe (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))
        (Flat.Serial.Spine.loop s.tail).graph (point (finish label) token) =
      Part.some (point (finish label) token) := by
  simp only [observe, Flat.Serial.Spine.graph, Flat.Serial.Spine.code, NestedTheta.Term.toTerm_toGraph]
  rw [Wires.lift_denote (ε := ε)]
  have done := ExplicitRuntime.graph_completed (ε := ε) s.tail label token
  simpa only [observe, ExplicitRuntime.graph, NestedTheta.Term.toTerm_toGraph] using done

private theorem tail_observe (s : Shape Φ ε A M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (c : TyDen (Carrier M E D)) (token : σ) :
    observe (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))
        (Flat.Serial.Spine.loop s.tail).graph (point c token) =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        (((match TypeModel.coprodEquiv (ExitCode E D) M c with
          | .inl label => pure (exitLabel (TypeModel.coprodEquiv E D label))
          | .inr payload => Region.denote (ε := ε) (m := StateT σ Part.{u})
              (Flat.Fragment.loop s.tail).typing (PUnit.unit, payload)) : StateT σ Part.{u} _).run token) := by
  have unpacked := (TypeModel.coprodEquiv (ExitCode E D) M).symm_apply_apply c
  cases h : TypeModel.coprodEquiv (ExitCode E D) M c with
  | inl label =>
    rw [h] at unpacked
    have eq : finish (A := M) (TypeModel.coprodEquiv E D label) = c := by
      simpa only [finish, Equiv.symm_apply_apply] using unpacked
    rw [← eq, tail_completed]
    simp only [StateT.run_pure, Part.pure_eq_some, Part.map_some]
    cases TypeModel.coprodEquiv E D label <;> rfl
  | inr x =>
    rw [h] at unpacked
    rw [← unpacked]
    exact (Flat.Serial.Spine.loop s.tail).agrees coherent (PUnit.unit,x) token

theorem emit_observe (s : Shape Φ ε A M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) s.emit (PureGamma.entry env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.fragment.typing env).run initial) := by
  rw [Shape.emit, linkRecovered_observe, head_observe _ coherent, Shape.fragment, Flat.denote_link _ _ coherent]
  simp only [StateT.run_bind, Part.bind_eq_bind, Part.bind_assoc, Part.map_bind, Part.bind_map]
  congr 1
  funext r
  rw [Flat.Fragment.gateCarrier_denote _ _ coherent]
  simp only [callCase, bind_assoc, pure_bind, StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  congr 1
  funext p
  exact tail_observe s coherent p.1 p.2

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse.Proofs
