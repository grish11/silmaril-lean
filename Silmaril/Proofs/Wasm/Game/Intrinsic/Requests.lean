module

public import Silmaril.Wasm.Game.Intrinsic.Requests.Defs
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Wasm.Game.Env.Thms
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Behaviour.Semantics.V3

public section

namespace Silmaril.Proofs.Wasm.Game.Intrinsic.Requests

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Execution.Core Numerics SingleThreaded
open Silmaril.Wasm.Game.Intrinsic.Requests

variable {source : Module} {I : ScalarInstance} {op : I.F.Op} {n : Nat}
  {tree : Tree source I (I.exports.get op.1)} {store target : Store Nat} {thread : Thread}
  {moves : List (Move I.E I.F)}

theorem path_of_completes {P : Profile} (implementation : Realizes P n op tree store thread)
    (complete : Completes n op tree moves) :
    ∃ target, I.Path P (.running op store thread) moves (.idle target) ∧
      ∀ next, .inr (.ask next) ∉ moves := by
  induction implementation generalizing moves with
  | @done _ _ _ _ answer run result =>
    cases complete
    exact ⟨_, .cons (.oret run result (Answer.ofResult?_toResult answer)) (.nil _), by simp⟩
  | @ask _ _ _ _ request args _ run callout decode _ ih =>
    cases complete with
    | ask reply allowed tail =>
      obtain ⟨target, path, single⟩ := ih reply allowed tail
      exact ⟨target, .cons (.ucall run callout decode)
        (.cons (.uret (e := request.question args) reply) path), by simpa⟩

private theorem idle_nil {P : Profile} (path : I.Path P (.idle store) moves (.idle target))
    (single : ∀ next, .inr (.ask next) ∉ moves) : moves = [] := by
  cases path with
  | nil => rfl
  | cons first _ =>
    cases first with
    | call _ next => exact (single next (List.Mem.head _)).elim

theorem completes_of_path {oracle : GrowOracle}
    (implementation : Realizes (profile oracle) n op tree store thread)
    (path : I.Path (profile oracle) (.running op store thread) moves (.idle target))
    (single : ∀ next, .inr (.ask next) ∉ moves) (legal : I.PlayThrowsBelow n moves) :
    Completes n op tree moves := by
  induction implementation generalizing moves with
  | @done _ actualStore _ final answer run result =>
    cases path with
    | @cons _ next _ move tail first rest =>
      have expected : I.Trans (profile oracle) _ (.inr (.ans op answer)) (.idle actualStore) :=
        .oret run result (Answer.ofResult?_toResult answer)
      have same := ScalarInstance.Trans.player_unique expected first (by simp [Move.IsP])
      subst move
      obtain rfl := ScalarInstance.Trans.functional expected first
      obtain rfl := idle_nil rest (fun other member => single other (.tail _ member))
      exact .done answer
  | @ask _ actualStore _ waiting request args then_ run callout decode _ ih =>
    cases path with
    | @cons _ next _ move tail first rest =>
      have expected : I.Trans (profile oracle) _ (.inl (.ask (request.question args)))
          (.waiting op actualStore waiting (request.question args)) := .ucall run callout decode
      have same := ScalarInstance.Trans.player_unique expected first (by simp [Move.IsP])
      subst move
      obtain rfl := ScalarInstance.Trans.functional expected first
      cases rest with
      | cons replyStep remaining =>
        cases replyStep with
        | uret reply =>
          have allowed := legal (request.question args) reply (.tail _ (.head _))
          exact .ask reply allowed (ih reply allowed remaining
            (fun other member => single other (.tail _ (.tail _ member)))
            (fun question answer member => legal question answer (.tail _ (.tail _ member))))

private theorem diverging_callout {P : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {thread : Thread} {slot : Nat} {args : List Val}
    (callout : CalloutAt store thread slot args) (silent : host slot store args .diverged) :
    Diverges P host (thread.config store) := by
  obtain ⟨eval, address, found⟩ := callout
  have step : Step P host (thread.config store) (thread.config store) := by
    obtain ⟨_, _, _, _, lookup, isHost, shape, expandable, arity, code⟩ := decompose?_sound found
    rw [Thread.config_eta store thread, code]
    exact eval.step_fill (fun _ => Step.callRefHostDiv shape lookup expandable arity isHost silent) _
  exact ⟨fun _ => thread.config store, rfl, fun _ => step⟩

theorem handled_mem_core {P : Profile} (implementation : Realizes P n op tree store thread)
    (env : Env I.E) (legal : ThrowsBelow env n) :
    tree.handledBehaviour env ∈ behavioursOf P (hostOf I.imports env) (thread.config store) := by
  induction implementation with
  | @done _ _ _ _ answer run result =>
    exact mem_behavioursOf run.steps result
  | @ask _ callStore _ _ request args then_ run callout decode _ ih =>
    apply behavioursOf_mono_steps run.steps
    cases selected : env (request.question args) with
    | none =>
      have silent : hostOf I.imports env request.slot.val callStore args.val .diverged :=
        (hostOf_iff _ _ _ _ _ _).mpr ⟨_, decode, by simp only [selected]⟩
      rw [Tree.handledBehaviour, Tree.handle, selected]
      exact diverges_mem_behavioursOf_iff.mpr (diverging_callout callout silent)
    | some reply =>
      have returns : hostOf I.imports env request.slot.val callStore args.val
          (.returned callStore reply.toResult) :=
        (hostOf_iff _ _ _ _ _ _).mpr ⟨_, decode, by simp only [selected]⟩
      have later := ih reply (legal _ _ selected)
      rw [Tree.handledBehaviour, Tree.handle, selected]
      exact behavioursOf_mono_steps (Relation.ReflTransGen.single (calloutAt_step callout returns)) later

end Silmaril.Proofs.Wasm.Game.Intrinsic.Requests
