module

public import Silmaril.Semantics.Brookes.TreeSC.Closed.Defs
public import Silmaril.Semantics.Brookes.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.TreeSC
open Silmaril.Semantics.TrackA.Interaction

variable {R : Type} [DecidableEq R]
variable {B : Signature} {A C I X : Type*}

theorem forestBehavior_eq_union (forest : Forest (signature R) B A I) :
    forestBehavior forest = behaviorUnion (fun i => treeBehavior forest.unfold (forest.root i)) := by
  apply Behavior.ext
  intro word result
  constructor
  · rintro ⟨seed, ⟨hne, s, frames, t, ⟨i, path⟩, eq⟩, steps⟩
    exact ⟨i, seed, ⟨hne, s, frames, t, path, eq⟩, steps⟩
  · rintro ⟨i, seed, ⟨hne, s, frames, t, path, eq⟩, steps⟩
    exact ⟨seed, ⟨hne, s, frames, t, ⟨i, path⟩, eq⟩, steps⟩

theorem choiceBehavior_eq_union {n : Nat} (kind : ChoiceKind) (code : Fin n → Code R) :
    forestBehavior (choose kind code) = behaviorUnion (fun i => machineBehavior (code i)) := by
  apply Behavior.ext
  intro word result
  cases result
  constructor
  · rintro ⟨seed, ⟨hne, s, frames, t, path, eq⟩, steps⟩
    obtain ⟨i, run⟩ := choice_returns_iff_machine.mp path
    exact ⟨i, seed, ⟨hne, s, frames, t, run, eq⟩, steps⟩
  · rintro ⟨i, seed, ⟨hne, s, frames, t, run, eq⟩, steps⟩
    exact ⟨seed, ⟨hne, s, frames, t, choice_returns_iff_machine.mpr ⟨i, run⟩, eq⟩, steps⟩

theorem treeBehavior_refines {D : Signature} {Y : Type*}
    {tree : Coalgebra (signature R) B A X} {other : Coalgebra (signature R) D A Y}
    {root : X} {otherRoot : Y} (refines : Refines (tree.observes root) (other.observes otherRoot))
    {word : Silmaril.Semantics.Brookes.Trace (Store R)} {result : A} (h : (treeBehavior tree root).accepts word result) :
    (treeBehavior other otherRoot).accepts word result := by
  obtain ⟨seed, ⟨hne, s, frames, t, ⟨y, z, ⟨path, stores⟩, silent, ret⟩, eq⟩, steps⟩ := h
  obtain ⟨y', z', path', silent', ret'⟩ :=
    refines (show Silmaril.Semantics.TrackA.Interaction.Trace.finite (frames.map Frame.exchange) (.returned result)
      ∈ tree.observes root from ⟨y, z, path, silent, ret⟩)
  exact ⟨seed, ⟨hne, s, frames, t, ⟨y', z', ⟨path', stores⟩, silent', ret'⟩, eq⟩, steps⟩

omit [DecidableEq R] in
private theorem internal_of_branch {tree : Coalgebra (signature R) B A X} {root y : X}
    {kind : ChoiceKind} {shape : B.Request} {next : B.Response shape → X}
    (layer : tree root = .branch kind shape next) (edge : tree.Internal root y) :
    ∃ i, y = next i := by
  rcases edge with step | ⟨_, _, i, step⟩
  · cases step with
    | tau other => exact nomatch layer.symm.trans other
  · cases step with
    | choice other _ =>
      have eq := layer.symm.trans other
      injection eq with _ shapeEq nextEq
      cases shapeEq
      cases nextEq
      exact ⟨i, rfl⟩

omit [DecidableEq R] in
private theorem branch_no_exchange {tree : Coalgebra (signature R) B A X} {root y : X}
    {kind : ChoiceKind} {shape : B.Request} {next : B.Response shape → X}
    (layer : tree root = .branch kind shape next) {e : (signature R).Exchange} :
    ¬ tree.Step root (.exchange e) y := by
  intro step
  cases step with
  | vis other _ => exact nomatch layer.symm.trans other

private theorem returns_branch_iff {tree : Coalgebra (signature R) B A X} {root : X}
    {kind : ChoiceKind} {shape : B.Request} {next : B.Response shape → X}
    (layer : tree root = .branch kind shape next) {gap : Gap R} {s t : Store R}
    {frames : List (Frame R)} {result : A} :
    Returns tree gap root s frames result t ↔ ∃ i, Returns tree gap (next i) s frames result t := by
  have edge (i : B.Response shape) : tree.Internal root (next i) :=
    .inr ⟨kind, shape, i, .choice layer i⟩
  cases frames with
  | nil =>
    constructor
    · rintro ⟨_, z, ⟨path, stores⟩, silent, ret⟩
      cases path
      rcases silent.cases_head with rfl | ⟨_, first, rest⟩
      · exact nomatch layer.symm.trans ret
      · obtain ⟨i, rfl⟩ := internal_of_branch layer first
        exact ⟨i, _, z, ⟨.nil _, stores⟩, rest, ret⟩
    · rintro ⟨i, _, z, ⟨path, stores⟩, silent, ret⟩
      cases path
      exact ⟨root, z, ⟨.nil _, stores⟩, silent.head (edge i), ret⟩
  | cons frame frames =>
    constructor
    · rintro ⟨y, z, ⟨path, stores⟩, silent, ret⟩
      cases path with
      | cons weak tail =>
        obtain ⟨_, pre, visible⟩ := weak
        rcases pre.cases_head with rfl | ⟨_, first, rest⟩
        · exact (branch_no_exchange layer visible).elim
        · obtain ⟨i, rfl⟩ := internal_of_branch layer first
          exact ⟨i, y, z, ⟨.cons ⟨_, rest, visible⟩ tail, stores⟩, silent, ret⟩
    · rintro ⟨i, y, z, ⟨path, stores⟩, silent, ret⟩
      cases path with
      | cons weak tail =>
        obtain ⟨mid, pre, visible⟩ := weak
        exact ⟨y, z, ⟨.cons ⟨mid, pre.head (edge i), visible⟩ tail, stores⟩, silent, ret⟩

theorem treeBehavior_branch {tree : Coalgebra (signature R) B A X} {root : X}
    {kind : ChoiceKind} {shape : B.Request} {next : B.Response shape → X}
    (layer : tree root = .branch kind shape next) :
    treeBehavior tree root = behaviorUnion (fun i => treeBehavior tree (next i)) := by
  apply Behavior.ext
  intro word result
  constructor
  · rintro ⟨seed, ⟨hne, s, frames, t, h, eq⟩, steps⟩
    obtain ⟨i, path⟩ := (returns_branch_iff layer).mp h
    exact ⟨i, seed, ⟨hne, s, frames, t, path, eq⟩, steps⟩
  · rintro ⟨i, seed, ⟨hne, s, frames, t, h, eq⟩, steps⟩
    exact ⟨seed, ⟨hne, s, frames, t, (returns_branch_iff layer).mpr ⟨i, h⟩, eq⟩, steps⟩

omit [DecidableEq R] in
private theorem map_step_iff (f : A → C) (tree : Coalgebra (signature R) B A X)
    {x y : X} {action : Coalgebra.Action (signature R) B} :
    (mapReturns f tree).Step x action y ↔ tree.Step x action y := by
  constructor
  · intro step
    cases step with
    | tau layer =>
      apply Coalgebra.Step.tau
      unfold mapReturns at layer
      generalize tree x = node at layer ⊢
      cases node <;> cases layer
      rfl
    | choice layer i =>
      refine Coalgebra.Step.choice ?_ i
      unfold mapReturns at layer
      generalize tree x = node at layer ⊢
      cases node <;> cases layer
      rfl
    | vis layer reply =>
      refine Coalgebra.Step.vis ?_ reply
      unfold mapReturns at layer
      generalize tree x = node at layer ⊢
      cases node <;> cases layer
      rfl
  · intro step
    cases step with
    | tau layer => exact .tau (by simp [mapReturns, layer])
    | choice layer i => exact .choice (by simp [mapReturns, layer]) i
    | vis layer reply => exact .vis (by simp [mapReturns, layer]) reply

omit [DecidableEq R] in
private theorem map_silent_iff (f : A → C) (tree : Coalgebra (signature R) B A X) {x y : X} :
    (mapReturns f tree).Silent x y ↔ tree.Silent x y := by
  have same (u v : X) : (mapReturns f tree).Internal u v ↔ tree.Internal u v := by
    simp only [Coalgebra.Internal, map_step_iff]
  exact ⟨Relation.ReflTransGen.mono (fun u v => (same u v).mp) x y,
    Relation.ReflTransGen.mono (fun u v => (same u v).mpr) x y⟩

omit [DecidableEq R] in
private theorem map_follows_iff (f : A → C) (tree : Coalgebra (signature R) B A X)
    {x y : X} {es : List (signature R).Exchange} :
    (mapReturns f tree).Follows x es y ↔ tree.Follows x es y := by
  have same {u v : X} {e : (signature R).Exchange} :
      (mapReturns f tree).WeakStep u e v ↔ tree.WeakStep u e v := by
    simp only [Coalgebra.WeakStep, map_silent_iff, map_step_iff]
  constructor
  · intro path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons (same.mp edge) ih
  · intro path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons (same.mpr edge) ih

theorem treeBehavior_map (f : A → C) (tree : Coalgebra (signature R) B A X) (root : X) :
    treeBehavior (mapReturns f tree) root = mapBehavior f (treeBehavior tree root) := by
  apply Behavior.ext
  intro word result
  constructor
  · rintro ⟨seed, ⟨hne, s, frames, t, ⟨y, z, ⟨path, stores⟩, silent, ret⟩, eq⟩, steps⟩
    unfold mapReturns at ret
    generalize layer : tree z = node at ret
    cases node with
    | ret a =>
      cases ret
      exact ⟨a, rfl, seed, ⟨hne, s, frames, t,
        ⟨y, z, ⟨(map_follows_iff f tree).mp path, stores⟩,
          (map_silent_iff f tree).mp silent, layer⟩, eq⟩, steps⟩
    | tau | vis | branch => cases ret
  · rintro ⟨a, rfl, seed, ⟨hne, s, frames, t, ⟨y, z, ⟨path, stores⟩, silent, ret⟩, eq⟩, steps⟩
    exact ⟨seed, ⟨hne, s, frames, t,
      ⟨y, z, ⟨(map_follows_iff f tree).mpr path, stores⟩,
        (map_silent_iff f tree).mpr silent, by simp [mapReturns, ret]⟩, eq⟩, steps⟩

end Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed
