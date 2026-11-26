module

public import Silmaril.Proofs.Semantics.Brookes.TreeSC.Replay

public section

namespace Silmaril.Proofs.Semantics.Brookes.TreeSC

open Silmaril.Semantics.Brookes.TreeSC
open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Semantics.TrackA.Concurrency (AccessMode)

variable {R : Type} {n : Nat} {kind : ChoiceKind} {code : Fin n → Code R}

private theorem ret_no_internal {S B : Signature} {A X : Type*} {c : Coalgebra S B A X}
    {x y : X} {a : A} (layer : c x = .ret a) : ¬ c.Internal x y := by
  rintro (step | ⟨_, _, _, step⟩)
  · cases step with
    | tau other => exact nomatch layer.symm.trans other
  · cases step with
    | choice other _ => exact nomatch layer.symm.trans other

private theorem vis_no_internal {S B : Signature} {A X : Type*} {c : Coalgebra S B A X}
    {x y : X} {q : S.Request} {k : S.Response q → X} (layer : c x = .vis q k) :
    ¬ c.Internal x y := by
  rintro (step | ⟨_, _, _, step⟩)
  · cases step with
    | tau other => exact nomatch layer.symm.trans other
  · cases step with
    | choice other _ => exact nomatch layer.symm.trans other

private theorem selected_done :
    choiceUnfold kind code (some (Code.toTree (.done : Code R))) = .ret () :=
  congrArg choiceLayer layer_done

private theorem selected_read (mode : AccessMode) (loc : R) (k : Nat → Code R) :
    choiceUnfold kind code (some (Code.toTree (.load mode loc k))) =
      .vis (Request.read mode loc) (fun r => some (Code.toTree (k r))) :=
  congrArg choiceLayer (layer_read mode loc k)

private theorem selected_write (mode : AccessMode) (loc : R) (v : Nat)
    (k : Code R) :
    choiceUnfold kind code (some (Code.toTree (.store mode loc v k))) =
      .vis (Request.write mode loc v) (fun _ => some k.toTree) :=
  congrArg choiceLayer (layer_write mode loc v k)

private theorem selected_silent {p : Code R} {y : Option (Tree R)}
    (silent : (choiceUnfold kind code).Silent (some p.toTree) y) : some p.toTree = y := by
  rcases silent.cases_head with same | ⟨_, first, _⟩
  · exact same
  · exfalso
    cases p with
    | done => exact ret_no_internal selected_done first
    | load mode loc k => exact vis_no_internal (selected_read mode loc k) first
    | store mode loc value k => exact vis_no_internal (selected_write mode loc value k) first
    | acquire lock | release lock => exact lock.elim

private theorem root_internal {y : Option (Tree R)}
    (edge : (choiceUnfold kind code).Internal none y) :
    ∃ i, y = some (code i).toTree := by
  have root : choiceUnfold kind code none = .branch kind n (fun i => some (code i).toTree) := rfl
  rcases edge with step | ⟨choice, shape, i, step⟩
  · cases step with
    | tau layer => exact nomatch root.symm.trans layer
  · cases step with
    | choice layer _ =>
      have same := root.symm.trans layer
      injection same with _ shapeEq nextEq
      cases shapeEq
      cases nextEq
      exact ⟨i, rfl⟩

private theorem select_root (i : Fin n) :
    (choiceUnfold kind code).Internal none (some (code i).toTree) :=
  Or.inr ⟨kind, n, i,
    Coalgebra.Step.choice (c := choiceUnfold kind code) (x := none)
      (kind := kind) (shape := n) (next := fun j => some (code j).toTree) rfl i⟩

private theorem root_cannot_exchange {e : (signature R).Exchange} {y : Option (Tree R)} :
    ¬ (choiceUnfold kind code).Step none (.exchange e) y := by
  intro step
  cases step with
  | vis layer _ =>
    have root : choiceUnfold kind code none = .branch kind n (fun i => some (code i).toTree) := rfl
    exact nomatch root.symm.trans layer

private theorem root_silent {y : Option (Tree R)} (silent : (choiceUnfold kind code).Silent none y) :
    y = none ∨ ∃ i, y = some (code i).toTree := by
  rcases silent.cases_head with rfl | ⟨mid, edge, rest⟩
  · exact Or.inl rfl
  · obtain ⟨i, rfl⟩ := root_internal edge
    exact Or.inr ⟨i, (selected_silent rest).symm⟩

private theorem selected_edge {p : Code R} {e : (signature R).Exchange} {y : Option (Tree R)} :
    (choiceUnfold kind code).WeakStep (some p.toTree) e y ↔
      ∃ tree, WeakITree.unfold.WeakStep p.toTree e tree ∧ y = some tree := by
  have selected : (choiceUnfold kind code).WeakStep (some p.toTree) e y ↔
      (choiceUnfold kind code).Step (some p.toTree) (.exchange e) y :=
    ⟨fun ⟨_, silent, step⟩ => selected_silent silent ▸ step, fun step => ⟨_, .refl, step⟩⟩
  rw [selected]
  constructor
  · intro step
    cases p with
    | acquire lock | release lock => exact lock.elim
    | done =>
      cases step with
      | vis layer _ => exact nomatch selected_done.symm.trans layer
    | load mode loc k =>
      obtain ⟨r, rfl, rfl⟩ := (step_vis_iff (selected_read (kind := kind) (code := code) mode loc k)).mp step
      exact ⟨_, ⟨_, .refl, .vis (layer_read mode loc k) r⟩, rfl⟩
    | store mode loc value k =>
      obtain ⟨r, rfl, rfl⟩ := (step_vis_iff (selected_write (kind := kind) (code := code) mode loc value k)).mp step
      exact ⟨_, ⟨_, .refl, .vis (layer_write mode loc value k) r⟩, rfl⟩
  · rintro ⟨tree, ⟨mid, silent, step⟩, rfl⟩
    have same : p.toTree = mid := weak_silent_eq silent
    subst mid
    cases step with
    | @vis request next layer r =>
      exact Coalgebra.Step.vis (c := choiceUnfold kind code) (x := some p.toTree)
        (q := request) (next := fun reply => some (next reply)) (congrArg choiceLayer layer) r

variable [DecidableEq R]

private theorem selected_replay {gap : Gap R} {p : Code R} {s last : Store R}
    {frames : List (Frame R)} {y : Option (Tree R)} :
    Follows (choiceUnfold kind code) gap (some p.toTree) s frames y last ↔
      ∃ q, MachineFollows gap p s frames q last ∧ y = some q.toTree := by
  induction frames generalizing p s y with
  | nil =>
    constructor
    · rintro ⟨path, stores⟩
      cases path
      cases stores
      exact ⟨_, .nil _ _, rfl⟩
    · rintro ⟨_, replay, rfl⟩
      cases replay
      exact ⟨.nil _, .nil _⟩
  | cons frame frames ih =>
    constructor
    · rintro ⟨path, stores⟩
      cases path with
      | cons edge tail =>
        cases stores with
        | cons admitted valid rest =>
          obtain ⟨_, weak, rfl⟩ := selected_edge.mp edge
          obtain ⟨_, step, rfl⟩ := machine_step_iff.mp ⟨weak, valid⟩
          obtain ⟨_, replay, rfl⟩ := ih.mp ⟨tail, rest⟩
          exact ⟨_, .cons admitted step replay, rfl⟩
    · rintro ⟨_, replay, rfl⟩
      cases replay with
      | cons admitted step rest =>
        obtain ⟨weak, valid⟩ := machine_step_iff.mpr ⟨_, step, rfl⟩
        obtain ⟨tail, stores⟩ := ih.mpr ⟨_, rest, rfl⟩
        exact ⟨.cons (selected_edge.mpr ⟨_, weak, rfl⟩) tail, .cons admitted valid stores⟩

omit [DecidableEq R] in
private theorem selected_return {p : Code R}
    (ends : choiceUnfold kind code (some p.toTree) = .ret ()) : p = .done := by
  cases p with
  | done => rfl
  | load mode loc k => exact nomatch (selected_read mode loc k).symm.trans ends
  | store mode loc v k => exact nomatch (selected_write mode loc v k).symm.trans ends
  | acquire lock | release lock => exact lock.elim

theorem choice_returns_iff_machine {gap : Gap R} {s last : Store R} {frames : List (Frame R)} :
    Returns (choiceUnfold kind code) gap none s frames () last ↔
      ∃ i, MachineFollows gap (code i) s frames .done last := by
  cases frames with
  | nil =>
    constructor
    · rintro ⟨_, _, ⟨path, stores⟩, suffix, ends⟩
      cases path
      rcases root_silent suffix with rfl | ⟨i, rfl⟩
      · cases ends
      · cases stores
        have same := selected_return ends
        exact ⟨i, same.symm ▸ MachineFollows.nil .done _⟩
    · rintro ⟨i, replay⟩
      generalize same : code i = p at replay
      cases replay
      exact ⟨none, _, ⟨.nil _, .nil _⟩, Relation.ReflTransGen.single (select_root i), by
        rw [same]
        exact selected_done⟩
  | cons frame frames =>
    constructor
    · rintro ⟨_, _, ⟨path, stores⟩, suffix, ends⟩
      cases path with
      | cons edge tail =>
        obtain ⟨mid, silent, step⟩ := edge
        rcases root_silent silent with rfl | ⟨i, rfl⟩
        · exact (root_cannot_exchange step).elim
        · obtain ⟨q, replay, rfl⟩ := selected_replay.mp
            ⟨.cons ⟨_, .refl, step⟩ tail, stores⟩
          rw [← selected_silent suffix] at ends
          obtain rfl := selected_return ends
          exact ⟨i, replay⟩
    · rintro ⟨i, replay⟩
      obtain ⟨path, stores⟩ := selected_replay (kind := kind) (code := code) |>.mpr ⟨_, replay, rfl⟩
      cases path with
      | cons edge tail =>
        obtain ⟨mid, silent, step⟩ := edge
        have fromRoot := Relation.ReflTransGen.head (select_root (kind := kind) (code := code) i) silent
        exact ⟨_, _, ⟨.cons ⟨mid, fromRoot, step⟩ tail, stores⟩, .refl, selected_done⟩

end Silmaril.Proofs.Semantics.Brookes.TreeSC
