module

public import Silmaril.Semantics.Brookes.Parallel.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms
public import Silmaril.Semantics.TrackA.Concurrency.Thms

public section

namespace Silmaril.Proofs.Process.ITreeTrace.SharedStore

open Silmaril.Semantics.Brookes (Behavior)
open Silmaril.Semantics.Brookes.TreeSC (Code Store readBehavior writeBehavior)
open Silmaril.Semantics.TrackA.Concurrency (Config Event Shared primitive replay)

variable {R : Type} [DecidableEq R]

/-- Extend the selected component's word with one operation. The other word
is retained, and the new first transition joins the old shuffle at its start. -/
private theorem prepend {A : Type} (code : Bool → Code R) (tid : Bool)
    {op : Behavior (Store R) A} {next : A → Code R} {reply : A} {s m t : Store R}
    (head : (code tid).denote = op.bind (fun value => (next value).denote))
    (step : op.completes s m reply)
    (tail : let residual := Function.update code tid (next reply)
      ((residual false).denote.parallel (residual true).denote).completes m t ((), ())) :
    ((code false).denote.parallel (code true).denote).completes s t ((), ()) := by
  obtain ⟨left, right, merged, acceptsLeft, acceptsRight, shuffle, runs⟩ :=
    Behavior.parallel_completes_iff.mp tail
  apply Behavior.parallel_completes_iff.mpr
  cases tid
  · simp [Function.update] at acceptsLeft acceptsRight
    have accepts : (code false).denote.accepts ((s, m) :: left) () := by
      rw [head]
      exact Behavior.bind_accepts_iff.mpr ⟨[(s, m)], left, reply, step, acceptsLeft, .refl _⟩
    exact ⟨_, _, _, accepts, acceptsRight, .left (s, m) shuffle, .cons runs⟩
  · simp [Function.update] at acceptsLeft acceptsRight
    have accepts : (code true).denote.accepts ((s, m) :: right) () := by
      rw [head]
      exact Behavior.bind_accepts_iff.mpr ⟨[(s, m)], right, reply, step, acceptsRight, .refl _⟩
    exact ⟨_, _, _, acceptsLeft, accepts, .right (s, m) shuffle, .cons runs⟩

private theorem replay_tail {schedule : List Bool} {tid : Bool} {start mid last : Config Bool Empty R}
    {event : Event Bool Empty R} {events : List (Event Bool Empty R)}
    (head : start.stepFor tid = some (event, mid))
    (run : replay start (tid :: schedule) = some (events, last)) :
    ∃ tail, replay mid schedule = some (tail, last) := by
  cases h : replay mid schedule with
  | none => simp [replay, head, h] at run
  | some result =>
    obtain ⟨tail, finish⟩ := result
    simp [replay, head, h] at run
    exact ⟨tail, congrArg (fun c => some (tail, c)) run.2⟩

theorem parallel_of_replay {schedule : List Bool} {code : Bool → Code R} {s t : Store R}
    {events : List (Event Bool Empty R)}
    (run : replay (Config.initial code s) schedule = some (events, Config.initial (fun _ => .done) t)) :
    ((code false).denote.parallel (code true).denote).completes s t ((), ()) := by
  induction schedule generalizing code s events with
  | nil =>
    rw [replay, Option.some.injEq, Prod.mk.injEq] at run
    have codes := congrArg Config.code run.2
    have stores := congrArg (fun config => config.shared.memory) run.2
    change code = (fun _ => .done) at codes
    change s = t at stores
    subst code
    subst t
    have idHere : (Behavior.ret (Store := Store R) ()).completes s s () :=
      Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩
    rw [Code.denote]
    exact Behavior.parallel_completes_iff.mpr
      ⟨[(s, s)], [(s, s)], [(s, s), (s, s)], idHere, idHere, .left (s, s) (.right (s, s) .nil),
        .cons (.cons (.nil _))⟩
  | cons tid schedule ih =>
    cases head : code tid with
    | acquire lock | release lock => exact lock.elim
    | done => simp [replay, Config.stepFor, Config.localState, Config.initial, head, primitive] at run
    | load mode loc next =>
      have edge : (Config.initial code s).stepFor tid = some (⟨tid, .read mode loc (s loc)⟩,
          Config.initial (Function.update code tid (next (s loc))) s) := by
        simp [Config.stepFor, Config.localState, Config.initial, head, primitive, Shared.initial]
      obtain ⟨_, tail⟩ := replay_tail edge run
      exact prepend code tid (op := readBehavior loc) (next := next) (by rw [head, Code.denote])
        (Behavior.atomic_completes_iff.mpr ⟨rfl, rfl⟩) (ih tail)
    | store mode loc value next =>
      have edge : (Config.initial code s).stepFor tid = some (⟨tid, .write mode loc value⟩,
          Config.initial (Function.update code tid next) (Function.update s loc value)) := by
        simp [Config.stepFor, Config.localState, Config.initial, head, primitive, Shared.initial]
      obtain ⟨_, tail⟩ := replay_tail edge run
      exact prepend code tid (op := writeBehavior loc value) (next := fun _ => next) (reply := ())
        (by rw [head, Code.denote]) (Behavior.atomic_completes_iff.mpr rfl) (ih tail)

end Silmaril.Proofs.Process.ITreeTrace.SharedStore
