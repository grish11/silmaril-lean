module

public import Silmaril.Process.ITreeTrace.SharedStore.Defs
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms
public import Silmaril.Semantics.TrackA.Concurrency.Thms

public section

namespace Silmaril.Proofs.Process.ITreeTrace.SharedStore

open Silmaril.Elgot.ITree (Visible out out_ret out_vis)
open Silmaril.Process.ITreeTrace (End Event Flatten Pool Program Returned)
open Silmaril.Process.ITreeTrace.SharedStore
open Silmaril.Semantics.Brookes.TreeSC (Code Frame Request Store denote_completes_iff_sc)
open Silmaril.Semantics.TrackA
open Concurrency (Config Shared primitive replay replay_iff sc)

variable {T R : Type} [DecidableEq T] [DecidableEq R]

private abbrev frame (req : Request R) (before : Store R) : Frame R :=
  ⟨⟨req, (access req before).1⟩, before, (access req before).2⟩

omit [DecidableEq R] in
private theorem pool_update (code : T → Code R) (tid : T) (next : Code R) :
    pool (Function.update code tid next) = Function.update (pool code) tid (program next) := by
  funext other
  by_cases same : other = tid <;> simp [same, pool, Function.update]

omit [DecidableEq T] [DecidableEq R] in
private theorem returned_iff {code : T → Code R} {values : T → Unit} :
    Returned (pool code) values ↔ ∀ tid, code tid = .done := by
  constructor
  · intro done tid
    have root := done tid
    cases h : code tid with
    | done => rfl
    | load | store => simp [pool, h, program, out_vis] at root
    | acquire lock | release lock => exact lock.elim
  · intro done tid
    simp [pool, done tid, program]

private theorem head_cases (code : T → Code R) (before : Store R) (tid : T) :
    (out (pool code tid) = Part.some (.ret ()) ∧ (Config.initial code before).stepFor tid = none) ∨
    ∃ (req : Request R) (resume : Request.Reply req → Program (signature R) Unit)
      (residual : T → Code R),
      out (pool code tid) = Part.some (.vis (Event.call (sig := signature R) req) resume) ∧
      (Config.initial code before).stepFor tid =
        some ((frame req before).event tid, Config.initial residual (access req before).2) ∧
      pool residual = Function.update (pool code) tid (resume (access req before).1) := by
  cases head : code tid with
  | done =>
    exact Or.inl ⟨by simp [pool, head, program], by simp [Config.stepFor, Config.localState,
      Config.initial, head, primitive]⟩
  | load mode loc next =>
    exact Or.inr ⟨.read mode loc, fun reply => program (next reply),
      Function.update code tid (next (before loc)),
      by
        rw [pool, head, program]
        exact out_vis _ _,
      by simp [Config.stepFor, Config.localState, Config.initial, head, primitive,
        Shared.initial, Frame.event, access],
      pool_update _ _ _⟩
  | store mode loc value next =>
    exact Or.inr ⟨.write mode loc value, fun _ => program next,
      Function.update code tid next,
      by
        rw [pool, head, program]
        exact out_vis _ _,
      by simp [Config.stepFor, Config.localState, Config.initial, head, primitive,
        Shared.initial, Frame.event, access],
      pool_update _ _ _⟩
  | acquire lock | release lock => exact lock.elim

/-- Compare call heads at the same store without transporting a reply along an
index equality. -/
private def completeHead (before : Store R) :
    Visible (Event (signature R)) Unit (Program (signature R) Unit) →
      Option (Frame R × Program (signature R) Unit)
  | .ret _ => none
  | .vis (.call req) resume => some (frame req before, resume (access req before).1)

private theorem sound_aux {schedule : List T} {trees : Pool (signature R) T Unit}
    {before after : Store R} {events : List (Concurrency.Event T Empty R)}
    {stop : End (signature R) T Unit}
    (run : Flatten kernel (fun tid label => label.event tid) schedule trees before events stop after)
    {code : T → Code R} (encoded : trees = pool code) (finished : stop = .returned fun _ => ()) :
    (events.map (·.thread)).Sublist schedule ∧
      replay (Config.initial code before) (events.map (·.thread)) =
        some (events, Config.initial (fun _ => .done) after) := by
  induction run generalizing code with
  | returned done =>
    rw [encoded] at done
    have allDone := returned_iff.mp done
    have same : code = fun _ => .done := funext allDone
    exact ⟨List.nil_sublist _, by simp [same, replay]⟩
  | exhausted | silent | blocked | exited => cases finished
  | @exchange tid schedule trees before req next label reply after trace stop final root step _ ih =>
    subst trees
    change label = frame req before ∧ _ at step
    obtain ⟨rfl, completion⟩ := step
    cases completion
    rcases head_cases code before tid with ⟨retRoot, _⟩ | ⟨q, resume, residual, callRoot, edge, update⟩
    · exact nomatch Part.some_inj.mp (retRoot.symm.trans root)
    have observed := congrArg (completeHead before) (Part.some_inj.mp (callRoot.symm.trans root))
    have same : frame q before = frame req before ∧
        resume (access q before).1 = next (access req before).1 :=
      Prod.mk.inj (Option.some.inj observed)
    have stores : (access q before).2 = (access req before).2 := congrArg Frame.after same.1
    have encoded' : Function.update (pool code) tid (next (access req before).1) = pool residual := by
      rw [← same.2, ← update]
    rw [same.1, stores] at edge
    obtain ⟨sublist, tail⟩ := ih encoded' finished
    change replay (Config.initial residual (access req before).2) (trace.map (·.thread)) = _ at tail
    refine ⟨sublist.cons_cons tid, ?_⟩
    change replay (Config.initial code before) (tid :: trace.map (·.thread)) = _
    simp [replay, edge, tail]
  | @skip tid _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨sublist, tail⟩ := ih encoded finished
    exact ⟨sublist.cons tid, tail⟩

theorem sound {schedule : List T} {code : T → Code R} {before after : Store R}
    {events : List (Concurrency.Event T Empty R)}
    (run : Completes schedule code before events after) :
    (events.map (·.thread)).Sublist schedule ∧
      replay (Config.initial code before) (events.map (·.thread)) =
        some (events, Config.initial (fun _ => .done) after) :=
  sound_aux run rfl rfl

theorem complete {schedule : List T} {code : T → Code R} {before after : Store R}
    {events : List (Concurrency.Event T Empty R)}
    (run : replay (Config.initial code before) schedule =
      some (events, Config.initial (fun _ => .done) after)) :
    Completes schedule code before events after := by
  induction schedule generalizing code before events with
  | nil =>
    rw [replay, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, same⟩ := run
    have codes := congrArg Config.code same
    have stores := congrArg (fun config => config.shared.memory) same
    change code = (fun _ => .done) at codes
    change before = after at stores
    subst code
    subst after
    exact .returned (returned_iff.mpr fun _ => rfl)
  | cons tid schedule ih =>
    rcases head_cases code before tid with ⟨_, edge⟩ | ⟨req, resume, residual, root, edge, update⟩
    · simp [replay, edge] at run
    simp only [replay, Option.bind_eq_bind, edge, Option.bind_some] at run
    cases tail : replay (Config.initial residual (access req before).2) schedule with
    | none => simp [tail] at run
    | some pair =>
      obtain ⟨tailEvents, last⟩ := pair
      simp [tail] at run
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
      have tailRun := ih tail
      unfold Completes at tailRun
      rw [update] at tailRun
      exact .exchange root (show kernel req before (frame req before) _ from ⟨rfl, rfl⟩) tailRun

theorem sc_iff {code : T → Code R} {before after : Store R}
    {events : List (Concurrency.Event T Empty R)} :
    (∃ schedule, Completes schedule code before events after) ↔
      sc.MTr (Config.initial code before) events (Config.initial (fun _ => .done) after) :=
  ⟨fun ⟨_, run⟩ => (replay_iff.mp (sound run).2).1,
    fun run => ⟨_, complete (replay_iff.mpr ⟨run, rfl⟩)⟩⟩

theorem singleton_iff_denote {code : Code R} {before after : Store R} :
    (∃ schedule events, Completes (T := Unit) schedule (fun _ => code) before events after) ↔
      code.denote.completes before after () := by
  rw [denote_completes_iff_sc]
  constructor
  · rintro ⟨schedule, events, run⟩
    exact ⟨events, sc_iff.mp ⟨schedule, run⟩⟩
  · rintro ⟨events, run⟩
    obtain ⟨schedule, h⟩ := sc_iff.mpr run
    exact ⟨schedule, events, h⟩

end Silmaril.Proofs.Process.ITreeTrace.SharedStore
