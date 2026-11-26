module

public import Silmaril.Semantics.Brookes.TreeSC.Defs
public import Silmaril.Semantics.TrackA.Interaction.WeakITree.Thms
public import Silmaril.Semantics.TrackA.Concurrency.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.TreeSC

open Silmaril.Semantics.Brookes.TreeSC
open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Semantics.TrackA.Concurrency

variable {R : Type}

noncomputable abbrev unfoldCode : Coalgebra (signature R) Signature.noChoice Unit (Tree R) :=
  WeakITree.unfold

theorem layer_done :
    unfoldCode (Code.toTree (.done : Code R)) = .ret () :=
  WeakITree.unfold_ret ()

theorem layer_read (mode : AccessMode) (loc : R) (k : Nat → Code R) :
    unfoldCode (Code.toTree (.load mode loc k)) =
      .vis (Request.read mode loc) (fun r => (k r).toTree) := by
  rw [Code.toTree]
  exact WeakITree.unfold_vis (S := signature R) (Request.read mode loc) _

theorem layer_write (mode : AccessMode) (loc : R) (v : Nat) (k : Code R) :
    unfoldCode (Code.toTree (.store mode loc v k)) =
      .vis (Request.write mode loc v) (fun _ => k.toTree) := by
  rw [Code.toTree]
  exact WeakITree.unfold_vis (S := signature R) (Request.write mode loc v) _

private theorem no_internal (p : Code R) (y : Tree R) :
    ¬ unfoldCode.Internal p.toTree y := by
  rintro (step | ⟨_, shape, _, _⟩)
  · cases step with
    | tau layer =>
      cases p with
      | done => exact nomatch layer_done.symm.trans layer
      | load mode loc k => exact nomatch (layer_read mode loc k).symm.trans layer
      | store mode loc v k => exact nomatch (layer_write mode loc v k).symm.trans layer
      | acquire l | release l => exact l.elim
  · exact shape.elim

theorem weak_silent_eq {p : Code R} {y : Tree R}
    (silent : unfoldCode.Silent p.toTree y) : p.toTree = y := by
  rcases silent.cases_head with same | ⟨next, edge, _⟩
  · exact same
  · exact (no_internal p next edge).elim

private theorem weak_iff_step {p : Code R} {e : (signature R).Exchange} {y : Tree R} :
    unfoldCode.WeakStep p.toTree e y ↔ unfoldCode.Step p.toTree (.exchange e) y := by
  exact ⟨fun ⟨_, silent, step⟩ => weak_silent_eq silent ▸ step, fun step => ⟨_, .refl, step⟩⟩

theorem step_vis_iff {S B : Signature} {A X : Type*} {c : Coalgebra S B A X}
    {x y : X} {e : S.Exchange} {q : S.Request} {k : S.Response q → X}
    (layer : c x = .vis q k) :
    c.Step x (.exchange e) y ↔ ∃ r, e = ⟨q, r⟩ ∧ y = k r := by
  constructor
  · intro step
    cases step with
    | vis other reply =>
      rw [layer] at other
      injection other with same next
      cases same
      cases next
      exact ⟨reply, rfl, rfl⟩
  · rintro ⟨r, rfl, rfl⟩
    exact .vis layer r

private theorem weak_read {mode : AccessMode} {loc : R} {k : Nat → Code R}
    {e : (signature R).Exchange} {y : Tree R} :
    unfoldCode.WeakStep (Code.toTree (.load mode loc k)) e y ↔
      ∃ v : Nat, e = ⟨Request.read mode loc, v⟩ ∧ y = (k v).toTree := by
  rw [weak_iff_step]
  exact step_vis_iff (layer_read mode loc k)

private theorem weak_write {mode : AccessMode} {loc : R} {v : Nat} {k : Code R}
    {e : (signature R).Exchange} {y : Tree R} :
    unfoldCode.WeakStep (Code.toTree (.store mode loc v k)) e y ↔
      e = ⟨Request.write mode loc v, ()⟩ ∧ y = k.toTree := by
  rw [weak_iff_step]
  have layer := layer_write mode loc v k
  constructor
  · intro step
    obtain ⟨⟨⟩, rfl, rfl⟩ := (step_vis_iff layer).mp step
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact (step_vis_iff layer).mpr ⟨(), rfl, rfl⟩

private theorem read_exchange_eq {mode mode' : AccessMode} {loc loc' : R} {v v' : Nat} :
    (⟨Request.read mode loc, v⟩ : (signature R).Exchange) = ⟨Request.read mode' loc', v'⟩ ↔
      mode = mode' ∧ loc = loc' ∧ v = v' := by
  constructor
  · intro same
    obtain ⟨rfl, rfl⟩ := Request.read.inj (congrArg Sigma.fst same)
    exact ⟨rfl, rfl, eq_of_heq (Sigma.mk.inj same).2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem write_exchange_eq {mode mode' : AccessMode} {loc loc' : R} {v v' : Nat} :
    (⟨Request.write mode loc v, ()⟩ : (signature R).Exchange) =
        ⟨Request.write mode' loc' v', ()⟩ ↔ mode = mode' ∧ loc = loc' ∧ v = v' := by
  constructor
  · exact fun same => Request.write.inj (congrArg Sigma.fst same)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem read_ne_write {mode mode' : AccessMode} {loc loc' : R} {v v' : Nat}
    {unitReply : Request.Reply (Request.write mode' loc' v')} :
    (⟨Request.read mode loc, v⟩ : (signature R).Exchange) ≠
        ⟨Request.write mode' loc' v', unitReply⟩ :=
  fun same => nomatch congrArg Sigma.fst same

variable [DecidableEq R]

theorem machine_step_iff {p : Code R} {frame : Frame R} {y : Tree R} :
    unfoldCode.WeakStep p.toTree frame.exchange y ∧ frame.Valid ↔
      ∃ q, MachineStep p frame q ∧ y = q.toTree := by
  obtain ⟨⟨request, reply⟩, before, after⟩ := frame
  cases p with
  | acquire l | release l => exact l.elim
  | done =>
    constructor
    · rintro ⟨edge, _⟩
      cases weak_iff_step.mp edge with
      | vis layer _ => exact nomatch layer_done.symm.trans layer
    · rintro ⟨_, step, _⟩
      simp [MachineStep, sequential, primitive] at step
  | load mode loc k =>
    cases request with
    | read mode' loc' =>
      change Nat at reply
      simp only [weak_read, read_exchange_eq, Frame.Valid, MachineStep, sequential, primitive,
        Frame.event, Shared.initial, Option.some.injEq, Prod.mk.injEq, Event.mk.injEq,
        Action.read.injEq, true_and, Shared.mk.injEq]
      aesop
    | write mode' loc' value =>
      constructor
      · rintro ⟨edge, _⟩
        obtain ⟨_, wrong, _⟩ := weak_read.mp edge
        exact (read_ne_write wrong.symm).elim
      · rintro ⟨_, step, _⟩
        simp [MachineStep, sequential, primitive, Frame.event] at step
  | store mode loc val k =>
    cases request with
    | read mode' loc' =>
      constructor
      · rintro ⟨edge, _⟩
        exact (read_ne_write (weak_write.mp edge).1).elim
      · rintro ⟨_, step, _⟩
        simp [MachineStep, sequential, primitive, Frame.event] at step
    | write mode' loc' value =>
      change Unit at reply
      cases reply
      simp only [weak_write, write_exchange_eq, Frame.Valid, MachineStep, sequential,
        primitive, Frame.event, Shared.initial, Option.some.injEq, Prod.mk.injEq,
        Event.mk.injEq, Action.write.injEq, true_and, Shared.mk.injEq]
      aesop

theorem follows_iff_machine {gap : Gap R} {p : Code R} {s last : Store R}
    {frames : List (Frame R)} {y : Tree R} :
    Follows WeakITree.unfold gap p.toTree s frames y last ↔
      ∃ q, MachineFollows gap p s frames q last ∧ y = q.toTree := by
  induction frames generalizing p s y with
  | nil =>
    constructor
    · rintro ⟨tree, stores⟩
      cases tree
      cases stores
      exact ⟨p, .nil _ _, rfl⟩
    · rintro ⟨_, run, rfl⟩
      cases run
      exact ⟨.nil _, .nil _⟩
  | cons frame frames ih =>
    constructor
    · rintro ⟨tree, stores⟩
      cases tree with
      | cons edge tail =>
        cases stores with
        | cons gapOk valid rest =>
          obtain ⟨q, step, rfl⟩ := machine_step_iff.mp ⟨edge, valid⟩
          obtain ⟨lastCode, run, rfl⟩ := ih.mp ⟨tail, rest⟩
          exact ⟨lastCode, .cons gapOk step run, rfl⟩
    · rintro ⟨_, run, rfl⟩
      cases run with
      | cons gapOk step tail =>
        obtain ⟨edge, valid⟩ := machine_step_iff.mpr ⟨_, step, rfl⟩
        obtain ⟨tree, stores⟩ := ih.mpr ⟨_, tail, rfl⟩
        exact ⟨.cons edge tree, .cons gapOk valid stores⟩

theorem returns_iff_machine {gap : Gap R} {p : Code R} {s last : Store R}
    {frames : List (Frame R)} :
    Returns WeakITree.unfold gap p.toTree s frames () last ↔
      MachineFollows gap p s frames .done last := by
  constructor
  · rintro ⟨_, _, path, silent, layer⟩
    obtain ⟨q, run, rfl⟩ := follows_iff_machine.mp path
    rw [← weak_silent_eq silent] at layer
    cases q with
    | done => exact run
    | load mode loc k => exact nomatch (layer_read mode loc k).symm.trans layer
    | store mode loc v k => exact nomatch (layer_write mode loc v k).symm.trans layer
    | acquire l | release l => exact l.elim
  · intro run
    exact ⟨_, _, follows_iff_machine.mpr ⟨.done, run, rfl⟩, .refl, layer_done⟩

private theorem step_has_frame {p q : Code R} {s last : Store R} {e : Event Unit Empty R}
    (step : (sequential ()).Tr (p, Shared.initial s) e (q, Shared.initial last)) :
    ∃ frame : Frame R, frame.before = s ∧ frame.after = last ∧
      frame.event () = e ∧ MachineStep p frame q := by
  cases p with
  | acquire l | release l => exact l.elim
  | done => simp [sequential, primitive] at step
  | load mode loc k =>
    have label : (⟨(), .read mode loc (s loc)⟩ : Event Unit Empty R) = e := by
      simpa [primitive, Shared.initial] using
        congrArg (Option.map Prod.fst) (show primitive () _ = some (e, _) from step)
    refine ⟨⟨⟨Request.read mode loc, s loc⟩, s, last⟩, rfl, rfl, label, ?_⟩
    subst e
    exact step
  | store mode loc v k =>
    have label : (⟨(), .write mode loc v⟩ : Event Unit Empty R) = e := by
      simpa [primitive, Shared.initial] using
        congrArg (Option.map Prod.fst) (show primitive () _ = some (e, _) from step)
    refine ⟨⟨⟨Request.write mode loc v, ()⟩, s, last⟩, rfl, rfl, label, ?_⟩
    subst e
    exact step

omit [DecidableEq R] in
private theorem initial_memory (shared : Shared Unit Empty R) :
    Shared.initial shared.memory = shared := by
  cases shared with
  | mk memory owner =>
    have same : (fun _ : Empty => (none : Option Unit)) = owner := by
      funext l
      exact l.elim
    simp [Shared.initial, same]

theorem closed_iff_sc {p q : Code R} {s last : Store R} {events : List (Event Unit Empty R)} :
    sc.MTr (Config.single (p, Shared.initial s)) events (Config.single (q, Shared.initial last)) ↔
      ∃ frames, frames.map (Frame.event ()) = events ∧ MachineFollows Eq p s frames q last := by
  rw [single_run_iff]
  constructor
  · induction events generalizing p s with
    | nil =>
      intro run
      have same := (Cslib.LTS.MTr.nil_iff _ _ _).mp run
      cases same
      exact ⟨[], rfl, .nil _ _⟩
    | cons event events ih =>
      intro run
      obtain ⟨⟨midCode, shared⟩, step, tail⟩ := Cslib.LTS.MTr.cons_iff.mp run
      rw [← initial_memory shared] at step tail
      obtain ⟨frame, pre, post, label, replayStep⟩ := step_has_frame step
      obtain ⟨frames, labels, replayTail⟩ := ih tail
      exact ⟨frame :: frames, by simp [label, labels],
        .cons pre.symm replayStep (post.symm ▸ replayTail)⟩
  · rintro ⟨frames, rfl, run⟩
    induction run with
    | nil => exact .refl
    | cons same step _ ih =>
      cases same
      exact .stepL step ih

end Silmaril.Proofs.Semantics.Brookes.TreeSC
