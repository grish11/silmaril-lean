module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Agreement

/-! # Agreement of the numbered γ handoff with typed LambdaSSA exit routing -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Y H B K M C J E D : τ}
variable {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Compose already admitted fragments at a typed exit cut. The bypass
keeps the producer's token; the consumer runs only on the second exit. -/
theorem splice_agrees (p : Code Φ A X Y H E M ps) (q : Code Φ M E D M E D qs)
    {left : Fragment Φ A E M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.linkBy left right routing) (splice p q).1.toGraph :=
  Proofs.splice_agrees p q hp hq coherent

theorem Source.agrees (s : Source Φ A B K M C J E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph :=
  splice_agrees (Spine.loop s.producer).code (Spine.loop s.consumer).code
    ((Spine.loop s.producer).agrees coherent) ((Spine.loop s.consumer).agrees coherent) coherent

variable {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A E M M E D (Signatures A E M D)}

theorem Related.region_returns_iff (w : Related A B K M C J E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial =
        Part.some (exit, final) :=
  match w with | .generated s => returns_of_agrees (s.agrees coherent) env exit initial final

theorem Related.region_undefined_iff (w : Related A B K M C J E D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none :=
  match w with | .generated s => undefined_of_agrees (s.agrees coherent) env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed
