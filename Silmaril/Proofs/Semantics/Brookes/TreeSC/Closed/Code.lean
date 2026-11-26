module

public import Silmaril.Semantics.Brookes.TreeSC.Closed.Defs
public import Silmaril.Semantics.Brookes.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.TreeSC
open Silmaril.Semantics.TrackA.Concurrency
open Silmaril.Semantics.TrackA.Interaction

variable {R : Type} [DecidableEq R]

theorem treeBehavior_eq_machine (code : Code R) :
    treeBehavior WeakITree.unfold code.toTree = machineBehavior code := by
  apply Behavior.ext
  intro word result
  cases result
  constructor
  · rintro ⟨seed, ⟨hne, start, frames, last, path, eq⟩, reduces⟩
    obtain ⟨frames', run, eq'⟩ := returnTrace_iff_machine.mp ⟨frames, path, eq⟩
    exact ⟨seed, ⟨hne, start, frames', last, run, eq'⟩, reduces⟩
  · rintro ⟨seed, ⟨hne, start, frames, last, run, eq⟩, reduces⟩
    obtain ⟨frames', path, eq'⟩ := returnTrace_iff_machine.mpr ⟨frames, run, eq⟩
    exact ⟨seed, ⟨hne, start, frames', last, path, eq'⟩, reduces⟩

private theorem machineBehavior_done :
    machineBehavior (.done : Code R) = Behavior.ret () := by
  apply Behavior.ext
  intro word result
  cases result
  rw [Behavior.ret_accepts_iff]
  constructor
  · rintro ⟨_, ⟨_, s, frames, _, run, rfl⟩, reduces⟩
    cases run with
    | nil => exact ⟨s, rfl, reduces⟩
    | cons _ step _ => simp [MachineStep, sequential, primitive] at step
  · rintro ⟨s, _, reduces⟩
    exact ⟨[(s, s)], ⟨by simp, s, [], s, .nil _ _, rfl⟩, reduces⟩

omit [DecidableEq R] in
private theorem trace_unprefix {start : Store R} (frame : Frame R) (frames : List (Frame R)) :
    Reduces ([frame.transition] ++ returnTrace frame.after frames)
      (returnTrace start (frame :: frames)) := by
  cases frames with
  | nil => exact (Reduces.refl _).tail (Rewrite.mumble [] [] frame.before frame.after frame.after)
  | cons => exact .refl _

/-- An atomic prefix contributes its pair, followed by the seed of the
selected continuation. A zero-operation continuation contributes an optional
stutter. Nonempty continuations admit arbitrary stores at the join. -/
private theorem machineBehavior_prefix {V : Type} {p : Code R} (next : V → Code R)
    (step : Store R → Store R → V → Prop) (active : p ≠ .done)
    (split : ∀ {frame q}, MachineStep p frame q →
      ∃ v, step frame.before frame.after v ∧ q = next v)
    (join : ∀ {s t v}, step s t v →
      ∃ frame, frame.transition = (s, t) ∧ MachineStep p frame (next v)) :
    machineBehavior p = (Behavior.atomic step).bind (fun v => machineBehavior (next v)) := by
  apply Behavior.ext
  intro word result
  rw [Behavior.bind_accepts_iff]
  constructor
  · rintro ⟨_, ⟨_, start, frames, last, run, rfl⟩, reduces⟩
    cases run with
    | nil => exact (active rfl).elim
    | @cons _ q _ _ _ frame tail _ head rest =>
      obtain ⟨v, effect, rfl⟩ := split head
      refine ⟨[frame.transition], returnTrace frame.after tail, v, ?_, ?_, ?_⟩
      · exact Behavior.atomic_accepts_iff.mpr ⟨_, _, effect, .refl _⟩
      · exact Behavior.generate_accepts (returnTrace_ne_nil _ _) ⟨_, _, last, rest, rfl⟩
      · exact (trace_unprefix frame tail).trans reduces
  · rintro ⟨left, _, v, hleft, ⟨_, ⟨_, start, frames, last, run, rfl⟩, hright⟩, reduces⟩
    obtain ⟨s, t, effect, hstep⟩ := Behavior.atomic_accepts_iff.mp hleft
    obtain ⟨frame, pair, head⟩ := join effect
    have toWord : Reduces ([frame.transition] ++ returnTrace start frames) word :=
      ((pair ▸ hstep).append hright).trans reduces
    generalize next v = residual at run head
    cases run with
    | nil =>
      apply (machineBehavior p).stable (source := [frame.transition]) ?_
        (((Reduces.refl _).tail (Rewrite.stutter [frame.transition] [] start)).trans toWord)
      exact Behavior.generate_accepts (by simp)
        ⟨frame.before, [frame], frame.after, .cons trivial head (.nil _ _), rfl⟩
    | @cons _ _ _ _ _ nextFrame tail _ nextStep rest =>
      apply (machineBehavior p).stable (source := frame.transition ::
        nextFrame.transition :: tail.map Frame.transition) ?_ toWord
      exact Behavior.generate_accepts (by simp)
        ⟨frame.before, frame :: nextFrame :: tail, last,
          .cons trivial head (.cons trivial nextStep rest), rfl⟩

private theorem split_read {mode : AccessMode} {loc : R} {k : Nat → Code R}
    {frame : Frame R} {q : Code R} (h : MachineStep (.load mode loc k) frame q) :
    ∃ v, frame.after = frame.before ∧ v = frame.before loc ∧ q = k v := by
  have eq := congrArg (Option.map Prod.snd)
    (show primitive () _ = some (_, (q, Shared.initial frame.after)) from h)
  simp [primitive, Shared.initial] at eq
  exact ⟨frame.before loc, eq.2.symm, rfl, eq.1.symm⟩

private theorem split_write {mode : AccessMode} {loc : R} {value : Nat} {k : Code R}
    {frame : Frame R} {q : Code R} (h : MachineStep (.store mode loc value k) frame q) :
    frame.after = Function.update frame.before loc value ∧ q = k := by
  have eq := congrArg (Option.map Prod.snd)
    (show primitive () _ = some (_, (q, Shared.initial frame.after)) from h)
  simp [primitive, Shared.initial] at eq
  exact ⟨eq.2.symm, eq.1.symm⟩

private theorem machineBehavior_read (mode : AccessMode) (loc : R) (next : Nat → Code R) :
    machineBehavior (.load mode loc next) =
      (readBehavior loc).bind (fun reply => machineBehavior (next reply)) := by
  apply machineBehavior_prefix next (fun s t v => t = s ∧ v = s loc) (by simp)
  · intro frame q h
    obtain ⟨v, stores, reply, rfl⟩ := split_read h
    exact ⟨v, ⟨stores, reply⟩, rfl⟩
  · intro s t v h
    obtain ⟨after, reply⟩ := h
    subst t
    subst v
    exact ⟨⟨⟨Request.read mode loc, s loc⟩, s, s⟩, rfl, rfl⟩

private theorem machineBehavior_write (mode : AccessMode) (loc : R) (value : Nat) (next : Code R) :
    machineBehavior (.store mode loc value next) =
      (writeBehavior loc value).bind (fun _ => machineBehavior next) := by
  apply machineBehavior_prefix (fun _ : Unit => next)
    (fun s t _ => t = Function.update s loc value) (by simp)
  · intro frame q h
    exact ⟨(), split_write h⟩
  · intro s t _ eq
    subst t
    exact ⟨⟨⟨Request.write mode loc value, ()⟩, s, Function.update s loc value⟩, rfl, rfl⟩

theorem machineBehavior_eq_denote (code : Code R) : machineBehavior code = code.denote := by
  induction code with
  | done => exact machineBehavior_done
  | load mode loc next ih =>
    rw [machineBehavior_read, Code.denote]
    simp only [ih]
  | store mode loc value next ih => rw [machineBehavior_write, Code.denote, ih]
  | acquire lock _ _ | release lock _ _ => exact lock.elim

theorem denote_seq (first second : Code R) :
    (first.seq second).denote = Command.seq first.denote second.denote := by
  induction first with
  | done => exact (Behavior.ret_bind () (fun _ => second.denote)).symm
  | load mode loc next ih =>
    simp only [Code.seq, Code.denote, ih, Command.seq, Behavior.bind_assoc]
  | store mode loc value next ih =>
    simp only [Code.seq, Code.denote, ih, Command.seq, Behavior.bind_assoc]
  | acquire lock _ _ | release lock _ _ => exact lock.elim

end Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed
