module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point packChoice carriedData resultData)
open OrderedRuntime.Structured (RuntimeValues)
open TwoBlock.TwoExit (enter callCase)
open PureGamma (Choice model OrderedModel)
open Sequential
open NestedTheta.Partial (observe)
open NestedTheta.ExplicitRuntime.PurePrefix (gamma_denote primitive_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ} {ps qs rows : List (Ports (OrderedRuntime.Structured.Ty τ))}

private abbrev ValueTuple (ports : Ports (OrderedRuntime.Structured.Ty τ)) :=
  Tuple (RuntimeValues (TyDen (τ := τ)) σ) ports

private theorem forward (p : Part (ValueTuple (σ := σ) (InputPorts A))) :
    p.bind (fun r => Part.some (point (r.get .head) (r.get (.tail .head)))) = p := by
  rw [Part.bind_some_eq_map]
  apply Part.map_id'
  intro r
  cases r with
  | cons payload rest =>
    cases rest with
    | cons token rest => cases rest; rfl

private theorem classifier (gate : TwoBlock.Instruction Φ A (Choice A)) (x : TyDen A) (token : σ) :
    (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (resultData A) (.effect (.classifyPayload gate))) (point x token) =
    Part.map (fun p : (TyDen A ⊕ TyDen A) × σ =>
      OrderedRuntime.Structured.decode (ts := OrderedTheta.results A) (packChoice (A := A) p.1, p.2))
      ((callCase (ε := ε) (m := StateT σ Part.{u}) gate x).run token) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := OrderedTheta.results A))
    ((callCase (ε := ε) (m := StateT σ Part.{u}) gate x >>= fun v => pure (packChoice v)).run token) = _
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem choice_observe (gate : TwoBlock.Instruction Φ A (Choice A)) (left : RawCode Φ ε A ps)
    (right : RawCode Φ ε A qs) (x : TyDen A) (token : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (choiceCode gate left right).1.toGraph (point x token) =
      ((callCase (ε := ε) (m := StateT σ Part.{u}) gate x).run token).bind (fun p =>
        match p.1 with
        | .inl a => observe (model (Φ := Φ) (ε := ε) (σ := σ)) left.1.toGraph (point a p.2)
        | .inr a => observe (model (Φ := Φ) (ε := ε) (σ := σ)) right.1.toGraph (point a p.2)) := by
  simp only [observe, NestedTheta.Term.toTerm_toGraph, choiceCode, primitive_denote, gamma_denote]
  change ((OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
    (.ordered (carriedData A) (resultData A) (.effect (.classifyPayload gate))) (point x token)).bind _ = _
  rw [classifier, Part.bind_map]
  congr 1
  funext p
  obtain ⟨tag, final⟩ := p
  cases tag with
  | inl a =>
    exact forward (σ := σ) (A := A)
      (left.1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ)) (point a final) PUnit.unit)
  | inr a =>
    exact forward (σ := σ) (A := A)
      (right.1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ)) (point a final) PUnit.unit)

theorem tree_observe (tree : Tree Φ ε A rows)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (token : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) tree.graph (point env.2 token) =
      Part.map (fun p => point (merge p.1) p.2)
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) tree.fragment.typing env).run token) := by
  induction tree generalizing env token with
  | theta s order =>
    change observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile order) (point env.2 token) =
      Part.map _ ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.fragment.typing env).run token)
    rw [s.region_observe order coherent, s.region_denote coherent, s.fragment_denote coherent]
    simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
      Part.bind_some_eq_map, Part.map_map]
    rfl
  | choice gate left right ihLeft ihRight =>
    rw [Tree.graph, Tree.code, choice_observe, Tree.fragment, Flat.denote_forkCase _ _ _ coherent]
    simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
    congr 1
    funext p
    rcases p with ⟨tag, final⟩
    cases tag with
    | inl x => exact ihLeft (PUnit.unit,x) final
    | inr x => exact ihRight (PUnit.unit,x) final

private theorem link_observe (head : Tree Φ ε A ps) (tail : Flat.Serial.Graph Φ A X Z L E D qs)
    (right : Flat.Fragment Φ A E D) (agrees : Flat.Serial.Agrees (ε := ε) (σ := σ) right tail)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (observe (model (Φ := Φ) (ε := ε) (σ := σ)) head.graph (point env.2 initial)).bind (fun p =>
      Flat.Serial.observe (ε := ε) (σ := σ) tail (p.get .head) (p.get (.tail .head))) =
        Part.map (ExplicitRuntime.exitTuple (A := L))
          ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Flat.link head.fragment right).typing env).run initial) := by
  rw [tree_observe head coherent, Flat.denote_link _ _ coherent]
  simp only [StateT.run_bind, Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext out
  exact agrees (PUnit.unit,merge out.1) out.2

private theorem recovered_agrees {tail : Flat.Serial.Graph Φ A X Z L E D qs} (f : Translation.Fibre .mixed tail)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Flat.Serial.Agrees (ε := ε) (σ := σ) f.fragment tail := by
  rcases f with ⟨_, witness⟩
  cases witness with
  | generated source =>
    exact StructuredCFG.WithNestedFeedback.Related.region_observe (.generated source) coherent

theorem emit_observe (c : Candidate Φ ε A L E D rows)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) c.emit (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) c.fragment.typing env).run initial) := by
  rcases c with ⟨headRows, tailRows, x, z, tree, tail, f, rfl⟩
  unfold Candidate.emit Candidate.fragment
  simp only
  rw [MixedContinuation.linkRecovered_observe, enterGraph_observe, Part.bind_eq_bind, Part.bind_map]
  exact link_observe tree tail f.fragment (recovered_agrees f coherent) coherent env initial

theorem compile_agrees (head : Tree Φ ε A ps) (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (compile head tail) (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Flat.link head.fragment tail.source).typing env).run initial) := by
  rw [compile, MixedContinuation.compile_observe, enterGraph_observe, Part.bind_eq_bind, Part.bind_map]
  exact link_observe head (Translation.compile (.mixed tail)) tail.source
    (fun env token => (Translation.Source.mixed tail).compile_observe coherent env token) coherent env initial

theorem compiled_denote (head : Tree Φ ε A ps)
    (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D qs) (f : Fibre (compile head tail))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial =
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (Flat.link head.fragment tail.source).typing env).run initial := by
  have recovered := f.wiring ▸ emit_observe f.shape coherent env initial
  have same := recovered.symm.trans (compile_agrees head tail coherent env initial)
  apply Part.ext
  intro output
  let encode := ExplicitRuntime.exitTuple (A := L) (E := E) (D := D) (σ := σ)
  have member (p : Part (LabelDen [E,D] × σ)) : encode output ∈ Part.map encode p ↔ output ∈ p := by
    rw [Part.mem_map_iff]
    simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right, encode]
  rw [← member, ← member, same]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured.Proofs
