module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point carried carriedData results resultData exit bodyTarget iter_boundary)
open OrderedRuntime.Structured (Threaded RuntimeValues)
open TwoBlock.TwoExit (callCase)
open NestedTheta (stepWith)
open NestedTheta.ExplicitRuntime.PurePrefix (primitive_denote pure_denote theta_denote)
open Silmaril.Elgot (iter)
open PureGamma (Choice model OrderedModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A : τ}

private theorem block_denotes (s : Loop Φ ε A) :
    RegionDenotes (m := StateT σ Part.{u}) ε s.blockTyping
      (fun env => s.step env.2 >>= fun result => pure (bodyTarget result)) := by
  have value := PureRow.typingAt_denotes (ε := ε) (σ := σ) s.value (Γ := [A,A]) (i := 0) rfl
  have test := PureRow.typingAt_denotes (ε := ε) (σ := σ) s.decide (Γ := [A,A,A]) (i := 1) rfl
  have payload := Denotes.var (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})
    (Γ := [A,A,A,A]) (i := 1) (A := A) rfl
  have done := RegionDenotes.br (h := (show Isotope.SSA.At [A,A] 1 A from rfl)) payload
  have again := RegionDenotes.br (h := (show Isotope.SSA.At [A,A] 0 A from rfl)) payload
  have block := RegionDenotes.let₁ value (.case test done again)
  refine Eq.mp (congrArg (RegionDenotes (m := StateT σ Part.{u}) ε s.blockTyping) ?_) block
  funext env
  simp only [PureRow.call_bottom s.value s.bottom, Env.get, pure_bind, Loop.step, callCase, bind_assoc]
  congr 1
  funext y
  cases TypeModel.coprodEquiv A A y <;>
    simp only [labelInject_eq_recursive, LabelValue.inject, bodyTarget, exit, Sum.map]
  all_goals rfl

theorem region_denote (s : Loop Φ ε A)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env =
      iter (s.step (σ := σ)) env.2 >>= fun a => pure (exit a) :=
  congrFun (TwoBlock.regionDenote_eq_of coherent
    (OrderedTheta.region_iterates_of_body s.blockTyping _ (block_denotes s))) env

private abbrev Point (A : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried A))

private theorem decision_denote (op : TwoBlock.Instruction Φ A (Choice A)) (x : TyDen A) (token : σ) :
    (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (resultData (Choice A)) (decision op)) (point x token) =
      Part.map (fun (v, next) => OrderedRuntime.Structured.decode (ExplicitRuntime.choiceData v, next))
        ((callCase (ε := ε) (m := StateT σ Part.{u}) op x).run token) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Choice A)))
    ((callCase (ε := ε) (m := StateT σ Part.{u}) op x >>= fun v =>
        pure (ExplicitRuntime.choiceData v)).run token) = _
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private noncomputable def wireStep (s : Loop Φ ε A) (pureFirst : Bool) :
    Point (σ := σ) A → Part (Point (σ := σ) A ⊕ Point (σ := σ) A) :=
  stepWith (fun x =>
    (s.body pureFirst).1.denoteOpenWith (model (Φ := Φ) (ε := ε) (σ := σ)) x PUnit.unit)

private theorem step_denote (s : Loop Φ ε A) (pureFirst : Bool) (input : TyDen A × σ) :
    wireStep s pureFirst (point input.1 input.2) =
      Elgot.StateT.body (s.step (σ := σ)) input >>= fun result =>
        pure (Sum.map (fun p => point p.1 p.2) (fun p => point p.1 p.2) result) := by
  obtain ⟨x, token⟩ := input
  unfold wireStep stepWith
  rw [Bind.kleisliRight]
  cases pureFirst <;> simp only [Loop.body, primitive_denote, pure_denote]
  all_goals
    change (((OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (resultData (Choice A)) (decision s.decide)) (point x token)).bind _).bind _ = _
    rw [decision_denote, Part.bind_map, Part.bind_assoc]
    simp only [Elgot.StateT.body, Loop.step, Function.comp_apply, StateT.run_bind, StateT.run_pure,
      Part.bind_eq_bind, Part.pure_eq_some, Part.bind_assoc]
    congr 1
    funext p
    rcases p with ⟨tag, next⟩
    cases tag <;> simp only [NestedTheta.Term.denoteOpenWith, Part.pure_eq_some, Part.bind_some]
    all_goals rfl

private theorem point_eta (r : Point (σ := σ) A) :
    point (r.get .head) (r.get (.tail .head)) = r := by
  cases r with
  | cons value tail =>
    cases tail with
    | cons token tail => cases tail; rfl

theorem graph_observe (s : Loop Φ ε A) (pureFirst : Bool) (x : TyDen A) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point x initial) =
      Part.map (fun (y, token) => point y token) ((iter (s.step (σ := σ)) x).run initial) := by
  have normalized : NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ))
      (s.compile pureFirst) (point x initial) = iter (wireStep s pureFirst) (point x initial) := by
    unfold NestedTheta.Partial.observe Loop.compile
    rw [NestedTheta.Term.toTerm_toGraph (s.code pureFirst).1]
    simp only [Loop.code, theta_denote, NestedTheta.Term.denoteOpenWith]
    change (iter (wireStep s pureFirst) (point x initial)).bind
      (fun r => Part.some (point (r.get .head) (r.get (.tail .head)))) = _
    simp only [point_eta, Part.bind_some_right]
  rw [normalized, Elgot.StateT.run_iter]
  rw [iter_boundary (Elgot.StateT.body (s.step (σ := σ))) (wireStep s pureFirst)
    (fun p => point p.1 p.2) (fun p => point p.1 p.2) (step_denote s pureFirst) (x, initial)]
  exact Part.bind_some_eq_map _ _

theorem agrees (s : Loop Φ ε A) (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point env.2 initial) =
      Part.map encodeExit ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial) := by
  rw [graph_observe, region_denote s coherent]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε (StateT σ Part.{u})] in
theorem mapped_exit_iff (r : Part (LabelDen [A] × σ)) (z : TyDen A) (final : σ) :
    Part.map encodeExit r = Part.some (point z final) ↔ r = Part.some (exit z, final) := by
  rw [Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  constructor
  · rintro ⟨⟨label, token⟩, member, eq⟩
    rcases label with payload | dead
    · have samePayload := congrArg (fun (x : Point (σ := σ) A) => x.get .head) eq
      have sameToken := congrArg (fun (x : Point (σ := σ) A) => x.get (.tail .head)) eq
      change payload = z at samePayload
      change token = final at sameToken
      simpa only [← samePayload, ← sameToken, exit] using member
    · exact dead.elim
  · intro member
    exact ⟨(exit z, final), member, rfl⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Proofs
