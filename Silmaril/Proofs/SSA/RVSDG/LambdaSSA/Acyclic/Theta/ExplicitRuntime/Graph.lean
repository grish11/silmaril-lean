module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Body

/-! # Observe the numbered θ after constructor-wise token threading -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (carried results carriedData resultData pack point packChoice)
open OrderedRuntime.Structured
open Silmaril.Elgot (iter)
open NestedTheta (stepWith)
open TwoBlock.TwoExit (Carrier Route ExitCode Pure headerPorts armPorts routeResult callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open LinearChain.Wiring (newest)
open Wiring (eval WireValues)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K E D : τ}

local notation "readWire" => OrderedRuntime.Structured.readOrigin (F := WireValues (τ := τ) (σ := σ))

private abbrev Point (Q : τ) := Tuple (WireValues (σ := σ)) (Threaded (carried Q))
private abbrev Result (Q : τ) := Tuple (WireValues (σ := σ)) (Threaded (results Q))

private def armInput (saved : TyDen (Carrier A E D)) (route : TyDen (Route B E D)) (state : σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (armPorts A B E D)) :=
  .cons saved (.cons route (.cons state .nil))

private def headerTuple (p : (TyDen E ⊕ TyDen B) × σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (headerPorts B E D)) :=
  OrderedRuntime.Structured.decode
    (routeResult (Sum.map (fun e => (TypeModel.coprodEquiv E D).symm (.inl e)) id p.1), p.2)

private def joinTuple (p : (TyDen D ⊕ TyDen A) × σ) : Result (σ := σ) (Carrier A E D) :=
  OrderedRuntime.Structured.decode (LinearChain.lastResult p.1, p.2)

private def tagged (p : (LabelDen [E,D] ⊕ TyDen A) × σ) : Result (σ := σ) (Carrier A E D) :=
  TwoBlock.ExplicitRuntime.Skeleton.tagged (enter (A := A) (C := E) (D := D))
    (fun label => finish (A := A) (exitPayload label)) p

private theorem finishStep_after {args : Ports (OrderedRuntime.Structured.Ty τ)} (a : Data args)
    (past : List (Ports (OrderedRuntime.Structured.Ty τ)))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) (output : Result (σ := σ) (Carrier A E D)) :
    eval (ε := ε) (Wiring.finishStep (Φ := Φ) (a := a) (A := A) (E := E) (D := D) past) entry (locals.snoc output) =
      Part.some output := by
  simp only [eval, Wiring.finishStep, NestedTheta.Term.denoteOpenWith, Part.pure_eq_some]
  change Part.some (Wires.read (withRuntime (nextRuntime past (results (Carrier A E D)))
    (.cons (newest .head past) (.cons (newest (.tail .head) past) .nil)))
    entry (locals.snoc output)) = _
  rw [read_appended, read_cons, read_cons, read_newest, read_newest, read_nextRuntime]
  cases output with
  | cons tag tail =>
    cases tail with
    | cons value tail =>
      cases tail with
      | cons token tail => cases tail; rfl

private theorem header_wire (s : Loop Φ A B K E D) (a : TyDen A) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData _) (resultData (Route B E D)) (.effect (.header s.header)))
      (point (enter a) state) =
      Part.map (headerTuple (D := D)) ((callCase (ε := ε) (m := StateT σ Part.{u}) s.header a).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := headerPorts B E D))
    (((match TypeModel.coprodEquiv (ExitCode E D) A (enter a) with
    | .inl out => pure (routeResult (.inl out))
    | .inr a => callCase (ε := ε) s.header a >>= fun xy =>
        pure (routeResult (Sum.map (fun e => (TypeModel.coprodEquiv E D).symm (.inl e)) id xy))) :
      StateT σ Part.{u} _).run state) = _
  rw [enter, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem join_wire (op : TwoBlock.Instruction Φ K (Silmaril.coprod D A)) (value : TyDen K) (state : σ) :
    (wireModel (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData _) (resultData (Carrier A E D)) (.effect (.join op)))
      (point value state) =
      Part.map (joinTuple (E := E)) ((callCase (ε := ε) (m := StateT σ Part.{u}) op value).run state) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Carrier A E D)))
    (((callCase (ε := ε) op value >>= fun result => pure (LinearChain.lastResult result)) :
        StateT σ Part.{u} _).run state) = _
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem exit_arm (saved : TyDen (Carrier A E D))
    (out : TyDen E ⊕ TyDen D) (state : σ) :
    eval (ε := ε) (Wiring.exitArm (Φ := Φ))
      (armInput (B := B) saved ((TypeModel.coprodEquiv (ExitCode E D) B).symm
        (.inl ((TypeModel.coprodEquiv E D).symm out))) state) PUnit.unit =
      Part.some (tagged (A := A) (D := D) (.inl (exitLabel out), state)) := by
  rw [Wiring.exitArm, eval_primitive]
  simp only [finishStep_after, Part.bind_eq_bind, Part.bind_some_right]
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Carrier A E D))) (Part.some
    ((match TypeModel.coprodEquiv (ExitCode E D) B ((TypeModel.coprodEquiv (ExitCode E D) B).symm
        (.inl ((TypeModel.coprodEquiv E D).symm out))) with
      | .inl out => packChoice (.inl ((TypeModel.coprodEquiv (ExitCode E D) A).symm (.inl out)))
      | .inr _ => packChoice (.inr saved)), state)) = _
  rw [Equiv.apply_symm_apply]
  cases out <;> rfl

private theorem body_arm (s : Loop Φ A B K E D) (saved : TyDen (Carrier A E D))
    (b : TyDen B) (state : σ) :
    eval (ε := ε) (Wiring.bodyArm s) (armInput saved (LinearChain.bodyRoute b) state) PUnit.unit =
      ((bodyAction (ε := ε) (m := StateT σ Part.{u}) s.body b).run state).bind
        (fun p => Part.map (joinTuple (E := E)) ((callCase (ε := ε) (m := StateT σ Part.{u}) s.join p.1).run p.2)) := by
  unfold Wiring.bodyArm
  apply emit_denote
  · change ((TypeModel.coprodEquiv (ExitCode E D) B (LinearChain.bodyRoute b)).getRight?) = _
    rw [LinearChain.bodyRoute, Equiv.apply_symm_apply]
    rfl
  · intro past live source locals
    rw [eval_primitive, read_appended, read_cons]
    change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _
      (point (readWire source _ locals)
        (readWire live _ locals)) >>= _) = _
    rw [join_wire]
    simp only [finishStep_after, Part.bind_eq_bind, Part.bind_some_right]

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (j : Fin 1) → F j.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private theorem activation_denote (s : Loop Φ A B K E D) (a : TyDen A) (state : σ) :
    eval (ε := ε) (Wiring.thetaBody s) (point (enter a) state) PUnit.unit =
      Part.map (tagged (A := A)) ((round (ε := ε) (m := StateT σ Part.{u}) s a).run state) := by
  rw [Wiring.thetaBody, eval_primitive]
  change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _ (point (enter a) state) >>= _) = _
  rw [header_wire s]
  simp only [round, StateT.run_bind, Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext p
  obtain ⟨result, token⟩ := p
  rw [eval_choice, read_appended, read_cons, read_cons, read_newest, read_newest, read_nextRuntime]
  simp only [finishStep_after, Part.bind_eq_bind, Part.bind_some_right]
  cases result with
  | inl e =>
    change eval (ε := ε) (Wiring.exitArm (Φ := Φ))
      (armInput (B := B) (enter a) ((TypeModel.coprodEquiv (ExitCode E D) B).symm
        (.inl ((TypeModel.coprodEquiv E D).symm (.inl e)))) token) PUnit.unit = _
    rw [exit_arm (Φ := Φ) (out := .inl e)]
    rfl
  | inr b =>
    change eval (ε := ε) (Wiring.bodyArm s) (armInput (enter a) (LinearChain.bodyRoute b) token)
      PUnit.unit = _
    rw [body_arm s]
    simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
    congr 1
    funext p
    rw [← Part.bind_some_eq_map]
    congr 1
    funext q
    rcases q with ⟨result, state⟩
    cases result <;> rfl

private def entry (p : TyDen A × σ) : Point (σ := σ) (Carrier A E D) :=
  point (enter p.1) p.2

private noncomputable def wireBody (s : Loop Φ A B K E D) (input : Point (σ := σ) (Carrier A E D)) :=
  eval (ε := ε) (Wiring.thetaBody s) input PUnit.unit

private theorem step_denote (s : Loop Φ A B K E D) (input : TyDen A × σ) :
    stepWith (wireBody (ε := ε) s) (entry input) =
      Silmaril.Elgot.StateT.body (round (ε := ε) (m := StateT σ Part.{u}) s) input >>= fun result =>
        pure (Sum.map exitTuple entry result) := by
  change stepWith (wireBody (ε := ε) s) (point (enter input.1) input.2) = _
  unfold stepWith
  rw [Bind.kleisliRight]
  change (wireBody (ε := ε) s (point (enter input.1) input.2) >>= _) = _
  unfold wireBody
  rw [activation_denote]
  simp only [Silmaril.Elgot.StateT.body, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨(out | next), state⟩ <;>
    simp only [Function.comp_apply, Part.pure_eq_some, Part.bind_some] <;> rfl

private theorem graph_iter (s : Loop Φ A B K E D) (input : Point (σ := σ) (Carrier A E D)) :
    NestedTheta.Partial.observe (wireModel (ε := ε)) (graph s) input =
      iter (stepWith (wireBody (ε := ε) (σ := σ) s)) input := by
  unfold NestedTheta.Partial.observe graph
  rw [NestedTheta.Term.toTerm_toGraph]
  simp only [Wiring.loop, NestedTheta.Term.denoteOpenWith, NestedTheta.ExplicitRuntime.thetaNode,
    NestedTheta.Kind.denoteWith, read_appended, read_cons, read_newest, read_nextRuntime]
  have forward (output : Point (σ := σ) (Carrier A E D)) :
      point (output.get .head) (output.get (.tail .head)) = output := by
    cases output with
    | cons a tail =>
      cases tail with
      | cons token tail => cases tail; rfl
  change (iter (stepWith (wireBody (ε := ε) (σ := σ) s)) (point (input.get .head) (input.get (.tail .head))) >>=
    fun output => pure (point (output.get .head) (output.get (.tail .head)))) = _
  simp only [forward, bind_pure]

theorem graph_observe (s : Loop Φ A B K E D) (a : TyDen A) (state : σ) :
    observe (ε := ε) (graph s) a state =
      Part.map (exitTuple (A := A)) ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run state) := by
  unfold observe
  rw [graph_iter, Silmaril.Elgot.StateT.run_iter]
  change iter _ (entry (a, state)) = _
  rw [OrderedTheta.iter_boundary _ _ entry exitTuple (step_denote s) (a, state)]
  exact Part.bind_some_eq_map _ _

theorem graph_completed (s : Loop Φ A B K E D) (out : TyDen E ⊕ TyDen D) (token : σ) :
    NestedTheta.Partial.observe (wireModel (ε := ε)) (graph s) (point (finish out) token) =
      Part.some (point (finish out) token) := by
  let input := point (finish (A := A) out) token
  let step := stepWith (wireBody (ε := ε) (σ := σ) s)
  have activate : wireBody (ε := ε) (σ := σ) s input =
      Part.some (tagged (A := A) (.inl (exitLabel out), token)) := by
    unfold wireBody input
    rw [Wiring.thetaBody, eval_primitive]
    let e := (TypeModel.coprodEquiv E D).symm out
    have head :
        (wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
          (.ordered (carriedData _) (resultData (Route B E D)) (.effect (.header s.header)))
          (point (finish out) token) =
            Part.some (OrderedRuntime.Structured.decode (ts := headerPorts B E D)
              (routeResult (.inl e), token)) := by
      change Part.map _ (((match TypeModel.coprodEquiv (ExitCode E D) A (finish out) with
        | .inl e => pure (routeResult (.inl e))
        | .inr a => callCase (ε := ε) s.header a >>= fun xy =>
            pure (routeResult (Sum.map (fun x => (TypeModel.coprodEquiv E D).symm (.inl x)) id xy))) :
        StateT σ Part.{u} _).run token) = _
      simp [finish, Equiv.apply_symm_apply, e]
    change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _ (point (finish out) token) >>= _) = _
    rw [head, Part.bind_eq_bind, Part.bind_some, eval_choice, read_appended, read_cons, read_cons,
      read_newest, read_newest, read_nextRuntime]
    simp only [finishStep_after, Part.bind_eq_bind, Part.bind_some_right]
    exact exit_arm (B := B) (finish out) out token
  rw [graph_iter, congrFun (Silmaril.Elgot.Part.fixpoint step) input]
  change ((wireBody (ε := ε) (σ := σ) s input >>= _) >>= _) = _
  rw [activate]
  simp only [Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some]
  cases out <;> rfl

theorem exitTuple_injective :
    Function.Injective (exitTuple (A := A) (E := E) (D := D) (σ := σ)) := by
  rintro ⟨a, state⟩ ⟨b, token⟩ h
  have payload := congrArg (fun x : Point (σ := σ) (Carrier A E D) => x.get .head) h
  have tokenEq : state = token := congrArg
    (fun x : Point (σ := σ) (Carrier A E D) => x.get (.tail .head)) h
  have same := (TypeModel.coprodEquiv E D).symm.injective
    (Sum.inl.inj ((TypeModel.coprodEquiv (ExitCode E D) A).symm.injective payload))
  have restore (label : LabelDen [E,D]) : exitLabel (exitPayload label) = label := by
    rcases label with e | d | impossible
    · rfl
    · rfl
    · exact nomatch impossible
  exact Prod.ext ((restore a).symm.trans ((congrArg exitLabel same).trans (restore b))) tokenEq

theorem returns_of_observe (g : Graph Φ A E D) (a : TyDen A) (initial final : σ)
    (label : LabelDen [E,D]) (p : Part (LabelDen [E,D] × σ))
    (h : observe (ε := ε) g a initial = Part.map (exitTuple (A := A)) p) :
    returns (ε := ε) g a initial label final ↔ p = Part.some (label, final) := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some]
  change observe (ε := ε) g a initial = _ ↔ _
  rw [h, Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  exact ⟨fun ⟨y, m, eq⟩ => exitTuple_injective eq ▸ m, fun m => ⟨_, m, rfl⟩⟩

theorem map_none_iff {P Q : Type u} (f : P → Q) (p : Part P) :
    Part.map f p = Part.none ↔ p = Part.none := by
  constructor
  · intro h
    rw [Part.eq_none_iff] at h ⊢
    intro x m
    exact h (f x) ((Part.mem_map_iff f).mpr ⟨x, m, rfl⟩)
  · rintro rfl
    exact Part.map_none f

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Proofs
