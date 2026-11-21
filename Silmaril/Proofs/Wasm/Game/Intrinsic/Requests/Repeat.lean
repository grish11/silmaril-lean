module

public import Silmaril.Wasm.Game.Intrinsic.Requests.Repeat.Defs
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Game.Env.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.Intrinsic.Requests.Repeat

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Execution.Core Numerics SingleThreaded
open Silmaril.Wasm.Game.Intrinsic.Requests

variable {source : Module} {instance_ : ScalarInstance} {request : NamedImport source instance_}
  {args : Typed request.signature.params} {reply : Typed request.signature.results}
  {profile_ : Profile} {store : Store Nat} {waiting : Thread}

theorem reply_step (loop : Repeat profile_ request args reply store waiting)
    (env : Env instance_.E) (answers : env.Answers (request.question args) (.values reply)) :
    Step profile_ (hostOf instance_.imports env) (waiting.config store)
      ((resumeResult store waiting (.values reply.val)).config store) :=
  calloutAt_step loop.callout ⟨request.question args, loop.decode, .inl ⟨.values reply, answers, rfl⟩⟩

private theorem number_path {State : Type} {edge : State → State → Prop} {start finish : State}
    (path : Relation.ReflTransGen edge start finish) :
    ∃ length, ∃ walk : Nat → State, walk 0 = start ∧ walk length = finish ∧
      ∀ index < length, edge (walk index) (walk (index + 1)) := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => finish, rfl, rfl, by simp⟩
  | @head initial next step _ ih =>
    obtain ⟨length, walk, first, last, regular⟩ := ih
    refine ⟨length + 1, (fun | 0 => initial | index + 1 => walk index), rfl, last, ?_⟩
    intro index bound
    cases index with
    | zero =>
      change edge initial (walk 0)
      rw [first]
      exact step
    | succ index => exact regular index (Nat.lt_of_succ_lt_succ bound)

theorem periodic_core (loop : Repeat profile_ request args reply store waiting)
    (env : Env instance_.E) (answers : env.Answers (request.question args) (.values reply)) :
    ∃ period > 0, ∃ trace : Nat → Config Nat, trace 0 = waiting.config store ∧
      (∀ time, Step profile_ (hostOf instance_.imports env) (trace time) (trace (time + 1))) ∧
      (∀ time, time % period ≠ 0 → Step profile_ Det.noHost (trace time) (trace (time + 1))) ∧
      ∀ cycle, trace (cycle * period) = waiting.config store ∧
        trace (cycle * period + 1) = (resumeResult store waiting (.values reply.val)).config store := by
  obtain ⟨length, walk, first, last, regular⟩ :=
    number_path (Reach.steps (host := Det.noHost) loop.restart)
  let period := length + 1
  let segment : Nat → Config Nat := fun | 0 => waiting.config store | time + 1 => walk time
  have wrap : segment period = segment 0 := last
  let trace := fun time => segment (time % period)
  have positive : 0 < period := Nat.succ_pos _
  have next (time : Nat) : trace (time + 1) = segment (time % period + 1) := by
    change segment ((time + 1) % period) = _
    rw [← Nat.mod_add_mod]
    have bound := Nat.mod_lt time positive
    by_cases hit : time % period + 1 = period
    · rw [hit, Nat.mod_self, wrap]
    · rw [Nat.mod_eq_of_lt (show time % period + 1 < period by omega)]
  have internal (time : Nat) (nonBoundary : time % period ≠ 0) :
      Step profile_ Det.noHost (trace time) (trace (time + 1)) := by
    rw [next]
    change Step profile_ Det.noHost (segment (time % period)) (segment (time % period + 1))
    have bound := Nat.mod_lt time positive
    cases phase : time % period with
    | zero => exact (nonBoundary phase).elim
    | succ index =>
      rw [phase] at bound
      exact regular index (Nat.lt_of_succ_lt_succ bound)
  refine ⟨period, positive, trace, by simp [trace, segment], ?_, internal, ?_⟩
  · intro time
    by_cases phase : time % period = 0
    · rw [next]
      change Step profile_ (hostOf instance_.imports env) (segment (time % period))
        (segment (time % period + 1))
      rw [phase]
      change Step profile_ (hostOf instance_.imports env) (waiting.config store) (walk 0)
      rw [first]
      exact reply_step loop env answers
    · exact Step.of_noHost _ (internal time phase)
  · intro cycle
    constructor
    · simp [trace, segment]
    · rw [next, Nat.mul_mod_left]
      exact first

theorem game_prefix {op : instance_.F.Op} (loop : Repeat profile_ request args reply store waiting)
    (enter : Reach profile_ (store, instance_.initThread op) (store, waiting)) (count : Nat) :
    .inr (.ask op) :: .inl (.ask (request.question args)) :: Repeat.moves request args reply count ∈
      instance_.strategy profile_ store := by
  have repeated (count : Nat) : instance_.Path profile_ (.waiting op store waiting (request.question args))
      (Repeat.moves request args reply count) (.waiting op store waiting (request.question args)) := by
    induction count with
    | zero => exact .nil _
    | succ count ih =>
      exact .cons (.uret (e := request.question args) (.values reply))
        (.cons (.ucall loop.restart loop.callout loop.decode) ih)
  exact ScalarInstance.mem_strategy_iff.mpr
    ⟨_, .cons (.call store op) (.cons (.ucall enter loop.callout loop.decode) (repeated count))⟩

end Silmaril.Proofs.Wasm.Game.Intrinsic.Requests.Repeat
