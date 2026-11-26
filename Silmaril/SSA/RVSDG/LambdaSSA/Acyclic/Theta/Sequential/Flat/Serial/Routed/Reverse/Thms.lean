module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Complete

/-! # Recovery and finite observations of the routed numbered graph -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse

open Numbered.Recognize (RightAssociated)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Graph Φ A E M M E D sigs} {r : Isotope.LambdaSSA.Region Φ}

/-- On the parser's right-associated form, recovery returns the exact flat
source constructed from the two decoded loops. -/
theorem recover_generated [DecidableEq τ] [DecidableEq Φ] (s : Source Φ A B K M C J E D)
    (hp : RightAssociated s.producer.body) (hq : RightAssociated s.consumer.body)
    (iso : NestedTheta.Graph.Isomorphic (Wires.Op Φ) g s.graph) :
    recover ⟨s.graph, iso⟩ = some ⟨s.source.region, .routed s iso⟩ :=
  Proofs.recover_generated s hp hq iso

/-- Every graph emitted by the forward compiler is accepted at its
representative, including loop bodies with other sequence associations. -/
theorem complete_generated [DecidableEq τ] [DecidableEq Φ] (s : Source Φ A B K M C J E D)
    (iso : NestedTheta.Graph.Isomorphic (Wires.Op Φ) g s.graph) :
    (recover ⟨s.graph, iso⟩).isSome = true :=
  Proofs.complete_generated s iso

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Related.region_observe (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) :=
  match w with
  | .routed s iso =>
    (NestedTheta.Partial.observe_iso iso (Wires.wireModel (ε := ε)) _).trans (s.agrees coherent env initial)

theorem Related.region_returns_iff (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (exit, final) :=
  match w with
  | .routed s iso =>
    (NestedTheta.Partial.returns_iso_iff iso (Wires.wireModel (ε := ε)) _ _).trans
      ((Routed.Related.generated s).region_returns_iff coherent env exit initial final)

theorem Related.region_undefined_iff (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  cases w with
  | routed s iso =>
    rw [show observe (ε := ε) g env.2 initial = observe (ε := ε) s.graph env.2 initial from
      NestedTheta.Partial.observe_iso iso (Wires.wireModel (ε := ε)) _]
    exact (Routed.Related.generated s).region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse
