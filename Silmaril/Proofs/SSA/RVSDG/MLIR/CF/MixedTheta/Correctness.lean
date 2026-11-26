module

public import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Defs
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Thms
import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Proofs

open Silmaril.MLIR
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.Elgot (iter)
open LambdaSSA.Acyclic.Theta.Translation
open LambdaSSA.OrderedTheta (point)
open Isotope.LetIter.ProofRelevant.Semantics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ Φ ε σ : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{0,0} τ] [InstructionModel Φ τ ε (StateT σ Part)]
variable {A : τ} {w : Width}
variable (codec : TyDen A ≃ BitVec w.val) (s : PureTheta.Loop Φ ε A) (pureFirst : Bool)

private def successor : TyDen A ⊕ TyDen A → CF.Frame (Label w)
  | .inl out => ⟨.exit, packet codec out⟩
  | .inr next => ⟨.activate, packet codec next⟩

theorem activation_result (input : Env [w]) (x : TyDen A) :
    eval (σ := σ) codec (activation s pureFirst) ((packet codec x).append input) =
      (s.step (σ := σ) x >>= fun route => pure (activationPacket codec route)) := by
  cases pureFirst <;>
    simp only [activation, Bool.false_eq_true, ite_false, ite_true,
      eval, Body.eval, packet, Env.append, Env.get, Equiv.symm_apply_apply, PureTheta.Loop.step,
      bind_assoc, pure_bind]
  all_goals
    congr 1
    funext route
    have valueEq := congrArg (LambdaSSA.PureRow.pureCall (σ := σ) s.value s.bottom) (codec.symm_apply_apply x)
    cases route with
    | inl _ =>
      first
      | rfl
      | exact congrArg (fun y => (pure (activationPacket codec (.inl y)) : StateT σ Part (Env [Pure.i1,w]))) valueEq
    | inr _ =>
      first
      | rfl
      | exact congrArg (fun y => (pure (activationPacket codec (.inr y)) : StateT σ Part (Env [Pure.i1,w]))) valueEq

private theorem activation_eval (input : Env [w]) (x : TyDen A) :
    ((emit (w := w) s pureFirst).block .activate).eval (eval (σ := σ) codec)
        ((packet codec x).append input) =
      (s.step (σ := σ) x >>= fun route => pure (.inl (successor codec route))) := by
  simp only [emit, CF.Ordered.Block.eval, activation_result, bind_assoc, pure_bind]
  congr 1
  funext route
  cases route <;> simp [activationPacket, packet, CF.Terminator.eval, CF.Edge.eval, Operands.eval, Env.get, successor]
  all_goals rfl

private abbrev runFrom (input : Env [w]) (fuel : Nat) (x : TyDen A) :
    StateT σ Part (Option (Env [w])) :=
  let cfg := emit (w := w) s pureFirst
  CF.Ordered.runBlock cfg.block (CF.Ordered.Block.eval (eval (σ := σ) codec)) input fuel
    (cfg.block .activate) ((packet codec x).append input)

private theorem runFrom_succ (input : Env [w]) (fuel : Nat) (x : TyDen A) (initial : σ) :
    (runFrom codec s pureFirst input (fuel + 1) x).run initial =
      (Elgot.StateT.body (s.step (σ := σ)) (x, initial)).bind (fun
        | .inl (out, final) => Part.some ((if fuel = 0 then none else some (packet codec out)), final)
        | .inr (next, live) => (runFrom codec s pureFirst input fuel next).run live) := by
  change (CF.Ordered.runBlock _ _ _ (fuel + 1) _ _ : StateT σ Part _).run initial = _
  rw [CF.Ordered.runBlock, activation_eval codec s pureFirst]
  simp only [bind_assoc, pure_bind, StateT.run_bind, Part.bind_eq_bind,
    Elgot.StateT.body, Function.comp_apply, Part.pure_eq_some, Part.bind_assoc, Part.bind_some]
  congr 1
  funext result
  rcases result with ⟨route, token⟩
  cases route with
  | inr next => rfl
  | inl out =>
    cases fuel <;> simp [successor, emit, CF.Ordered.runBlock, CF.Ordered.Block.eval, eval, Body.eval,
      packet, Operands.eval, Env.get, CF.Terminator.eval, StateT.run_pure, Part.pure_eq_some,
      Elgot.StateT.distribute]; rfl

private theorem packet_injective : Function.Injective (packet codec) := by
  intro x y same
  exact codec.injective (congrArg (fun env : Env [w] => env.get .here) same)

private theorem done_mem (fuel : Nat) (out expect : TyDen A) (token final : σ) :
    (some (packet codec expect), final) ∈
        Part.some ((if fuel = 0 then none else some (packet codec out)), token) →
      (out, token) = (expect, final) := by
  cases fuel with
  | zero => simp
  | succ fuel =>
    intro h
    have same : (some (packet codec out), token) = (some (packet codec expect), final) :=
      (Part.mem_some_iff.mp h).symm
    have storeEq : token = final := congrArg (fun p : Option (Env [w]) × σ => p.2) same
    exact Prod.ext (packet_injective codec (Option.some.inj (congrArg Prod.fst same))) storeEq

private theorem from_of_runs (input : Env [w]) {start finish : TyDen A × σ}
    (ran : Elgot.Part.Runs (Elgot.StateT.body (s.step (σ := σ))) start finish) :
    ∃ fuel, (some (packet codec finish.1), finish.2) ∈
      (runFrom codec s pureFirst input fuel start.1).run start.2 := by
  induction ran with
  | @done start finish last =>
    refine ⟨2, ?_⟩
    rw [runFrom_succ]
    exact Part.mem_bind last (by simp)
  | @more start next finish first _ ih =>
    obtain ⟨fuel, ran⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    rw [runFrom_succ]
    exact Part.mem_bind first ran

private theorem runs_iff_from (input : Env [w]) (x out : TyDen A) (initial final : σ) :
    Elgot.Part.Runs (Elgot.StateT.body (s.step (σ := σ))) (x, initial) (out, final) ↔
      ∃ fuel, (some (packet codec out), final) ∈ (runFrom codec s pureFirst input fuel x).run initial := by
  constructor
  · exact from_of_runs codec s pureFirst input
  · rintro ⟨fuel, ran⟩
    induction fuel generalizing x initial with
    | zero => simp [runFrom, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some] at ran
    | succ fuel ih =>
      rw [runFrom_succ] at ran
      obtain ⟨result, step, continuation⟩ := Part.mem_bind_iff.mp ran
      cases result with
      | inl finished =>
        rcases finished with ⟨word, store⟩
        exact .done (done_mem codec fuel word out store final continuation ▸ step)
      | inr next => exact .more step (ih next.1 next.2 continuation)

private theorem entry_succ (x : TyDen A) (fuel : Nat) :
    (emit (w := w) s pureFirst).run (eval (σ := σ) codec) (fuel + 1) (packet codec x) =
      runFrom codec s pureFirst (packet codec x) fuel x := by
  simp only [CF.Ordered.Cfg.run, CF.Ordered.runBlock, emit, CF.Ordered.Block.eval, eval, Body.eval,
    packet, Operands.eval, Env.get, pure_bind, CF.Terminator.eval, CF.Edge.eval]
  rfl

private theorem runs_iff_cfg (x out : TyDen A) (initial final : σ) :
    Elgot.Part.Runs (Elgot.StateT.body (s.step (σ := σ))) (x, initial) (out, final) ↔
      ∃ fuel, (some (packet codec out), final) ∈
        ((emit (w := w) s pureFirst).run (eval (σ := σ) codec) fuel (packet codec x)).run initial := by
  rw [runs_iff_from codec s pureFirst (packet codec x)]
  constructor
  · rintro ⟨fuel, ran⟩
    exact ⟨fuel + 1, by rw [entry_succ]; exact ran⟩
  · rintro ⟨fuel, ran⟩
    cases fuel with
    | zero => simp [CF.Ordered.Cfg.run, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some] at ran
    | succ fuel =>
      rw [entry_succ] at ran
      exact ⟨fuel, ran⟩

theorem returns_iff {g : PureTheta.Reverse.Graph Φ ε A} (f : PureTheta.Reverse.Fibre g)
    (input output : TyDen A) (initial final : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) =
        Part.some (point output final) ↔
      ∃ fuel, ((lower w f).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
        Part.some (some (packet codec output), final) := by
  rcases f with ⟨s, pureFirst, rfl⟩
  rw [s.step_observe pureFirst input initial, Part.eq_some_iff, Part.mem_map_iff]
  have point_inj : Function.Injective (fun p : TyDen A × σ => point p.1 p.2) := by
    intro x y same
    exact Prod.ext (congrArg (fun tuple => Tuple.get tuple .head) same)
      (congrArg (fun tuple => Tuple.get tuple (.tail .head)) same)
  have target := runs_iff_cfg codec s pureFirst input output initial final
  simp only [lower, Part.eq_some_iff]
  rw [← target, Elgot.StateT.run_iter]
  constructor
  · rintro ⟨found, member, same⟩
    have eq : found = (output, final) := point_inj same
    exact (Elgot.Part.mem_iter_iff _ _ _).mp (eq ▸ member)
  · intro ran
    exact ⟨(output, final), (Elgot.Part.mem_iter_iff _ _ _).mpr ran, rfl⟩

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Proofs
