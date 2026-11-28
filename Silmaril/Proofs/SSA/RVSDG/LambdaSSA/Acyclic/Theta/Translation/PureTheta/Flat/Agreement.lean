module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open Sequential
open OrderedTheta (point)
open TwoBlock.TwoExit (callCase)

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

theorem loop_fragment_denote (s : Loop Φ ε A)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u})
        s.fragment.typing env =
      iter s.step env.2 >>= fun y => pure (.inl y) := by
  rw [Loop.fragment, Flat.Fragment.bindChooseLoop_denote _ _ coherent]
  have step :
      (fun x => TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) s.value x >>= fun y =>
        callCase (ε := ε) s.decide x >>= fun tag =>
          pure (tag.elim (fun _ => Sum.inl y) (fun _ => Sum.inr y))) = s.step := by
    funext x
    simp only [PureRow.call_bottom s.value s.bottom, pure_bind, Loop.step]
    congr 1
  rw [step]

private theorem denote_congr {r s : Isotope.LambdaSSA.Region Φ} {Γ exits : List τ}
    (hr : Isotope.LambdaSSA.Region.HasType Γ r exits)
    (hs : Isotope.LambdaSSA.Region.HasType Γ s exits) (eq : r = s) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) hr =
      Region.denote (ε := ε) (m := StateT σ Part.{u}) hs := by
  subst s
  rfl

theorem link_observe {g : Reverse.Graph Φ ε A} {layout : Layout τ A X Z L E D sigs}
    {h : Flat.Serial.Graph Φ A X Z L E D sigs} (f : Link g layout h)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ))
      g (point env.2 initial)).bind (fun output =>
        Flat.Serial.observe (ε := ε) (σ := σ) h (output.get .head) (output.get (.tail .head))) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial) := by
  have next (input : Env [A]) (token : σ) :
      Flat.Serial.observe (ε := ε) h input.2 token =
        Part.map (ExplicitRuntime.exitTuple (A := L))
          ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.next.fragment.typing input).run token) := by
    rw [denote_congr f.next.fragment.typing f.next.typing f.next.fragment_region]
    exact f.next.region_observe coherent input token
  change _ = Part.map _
    ((Region.denote (ε := ε) (m := StateT σ Part.{u})
      (Flat.link f.first.loop.fragment f.next.fragment).typing env).run initial)
  rw [f.first.region_observe coherent, Flat.denote_link _ _ coherent, loop_fragment_denote _ coherent]
  have first :
      Region.denote (ε := ε) (m := StateT σ Part.{u}) f.first.typing env =
        iter f.first.loop.step env.2 >>= fun y => pure (OrderedTheta.exit y) := by
    cases f.first
    exact Loop.region_denote _ coherent env
  rw [first]
  simp only [bind_assoc, pure_bind]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map, Part.bind_map, Part.map_bind]
  congr 1
  funext result
  exact next (PUnit.unit, result.1) result.2

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Proofs
