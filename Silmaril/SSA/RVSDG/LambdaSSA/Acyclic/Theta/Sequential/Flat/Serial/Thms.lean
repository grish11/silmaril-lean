module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Agreement

/-! # Serial composition via exact numbered cuts and flat linking -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

section Certification
variable [DecidableEq τ] [DecidableEq Φ]
variable {p : Code Φ A X Y H M M ps} {q : Code Φ M I J L E D qs}
variable {g : Graph Φ A X Y L E D (Joined M I J ps qs)}

theorem Cut.certified (cut : Cut p q g) : certifyCut p q g = some cut := by
  obtain ⟨wiring⟩ := cut
  simp only [certifyCut, dite_eq_left wiring]

theorem rejectCut (different : joinedGraph p q ≠ g) : certifyCut p q g = none := by
  simp only [certifyCut, dite_eq_right different]

end Certification

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem loop_observe {B K : τ} (s : Loop Φ A B K E D) (input : TyDen A) (initial : σ) :
    observe (ε := ε) (Spine.loop s).graph input initial =
      ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph s) input initial :=
  Proofs.loop_observe s input initial

/-- The observed intermediate payload and token are exactly the next
graph's arguments. The structural carrier conversion does not alter state. -/
theorem splice_after (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    (input : TyDen A) (initial token : σ) (exit : LabelDen [M,M])
    (finished : observe (ε := ε) p.1.toGraph input initial =
      Part.some (ExplicitRuntime.exitTuple (A := H) (exit, token))) :
    observe (ε := ε) (joinedGraph p q) input initial = observe (ε := ε) q.1.toGraph (merge exit) token :=
  Proofs.splice_after p q input initial token exit finished

/-- A reusable binary semantic law for any two already admitted components
with the serial carrier interface. Both sides use the actual syntax and
ordered state; neither primitive actions nor block tables are combined into an opcode. -/
theorem splice_agrees (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    {left : Fragment Φ A M M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.link left right) (joinedGraph p q) :=
  Proofs.splice_agrees p q hp hq coherent

theorem Cut.agrees {p : Code Φ A X Y H M M ps} {q : Code Φ M I J L E D qs}
    {g : Graph Φ A X Y L E D (Joined M I J ps qs)} (cut : Cut p q g)
    {left : Fragment Φ A M M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.link left right) g :=
  cut.wiring ▸ splice_agrees p q hp hq coherent

/-- Finite returns of the actual numbered graph decompose across a
certified cut, with the same intermediate payload and token on both sides. -/
theorem Cut.returns_iff {p : Code Φ A X Y H M M ps} {q : Code Φ M I J L E D qs}
    {g : Graph Φ A X Y L E D (Joined M I J ps qs)} (cut : Cut p q g)
    {left : Fragment Φ A M M} {right : Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      ∃ (mid : LabelDen [M,M]) (token : σ), returns (ε := ε) p.1.toGraph env.2 initial mid token ∧
        returns (ε := ε) q.1.toGraph (merge mid) token exit final :=
  Proofs.cut_returns cut hp hq coherent env exit initial final

theorem Spine.agrees (s : Spine Φ A X Y L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph :=
  Proofs.spine_agrees s coherent

theorem returns_of_agrees {source : Fragment Φ A E D} {g : Graph Φ A X Y L E D sigs}
    (h : Agrees (ε := ε) (σ := σ) source g) (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) source.typing env).run initial =
        Part.some (exit, final) :=
  Proofs.returns_of_agrees h env exit initial final

theorem undefined_of_agrees {source : Fragment Φ A E D} {g : Graph Φ A X Y L E D sigs}
    (h : Agrees (ε := ε) (σ := σ) source g) (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) source.typing env).run initial = Part.none := by
  rw [h env initial]
  exact Proofs.map_none_iff _ _

variable {g : Graph Φ A X Y L E D sigs}

theorem Decomposition.agrees (d : Decomposition g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) d.recover g :=
  Eq.mp (congrArg (fun g => Agrees (ε := ε) (σ := σ) d.spine.source g) d.wiring) (d.spine.agrees coherent)

theorem Decomposition.region_returns_iff (d : Decomposition g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) d.recover.typing env).run initial =
        Part.some (exit, final) :=
  returns_of_agrees (d.agrees coherent) env exit initial final

theorem Decomposition.region_undefined_iff (d : Decomposition g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) d.recover.typing env).run initial = Part.none :=
  undefined_of_agrees (d.agrees coherent) env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial
