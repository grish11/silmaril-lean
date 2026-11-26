module

public import Silmaril.SSA.MLIR.SCF.Parallel.Defs
import Init.Data.List.Nat.Pairwise
import Init.Data.Nat.Div.Lemmas

public section

namespace Silmaril.MLIR.SCF.Parallel.Proofs

universe u v

theorem rank_lt_tripCount (space : IndexSpace) (rank : Nat) :
    rank < space.tripCount ↔ space.lower + rank * space.step < space.upper := by
  rw [IndexSpace.tripCount, Nat.lt_div_iff_mul_lt space.step_pos, Nat.add_sub_cancel]
  omega

theorem tripCount_eq_zero (space : IndexSpace) :
    space.tripCount = 0 ↔ space.upper ≤ space.lower := by
  have first := rank_lt_tripCount space 0
  simp only [Nat.zero_mul, Nat.add_zero] at first
  omega

theorem index_injective (space : IndexSpace) :
    ∀ {first second : space.Trip}, space.index first = space.index second → first = second := by
  intro first second equal
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right space.step_pos (Nat.add_left_cancel equal)

theorem enumeration_nodup {space : IndexSpace} (order : space.Enumeration) :
    order.val.Nodup :=
  order.property.symm.nodup (List.nodup_finRange _)

private theorem leaves_ne_nil {α : Type u} (tree : Tree α) : tree.leaves ≠ [] := by
  induction tree with
  | leaf input => simp [Tree.leaves]
  | fork left right ihLeft _ => simp [Tree.leaves, ihLeft]

private theorem leaves_appendLeaves {α : Type u} (tree : Tree α) (inputs : List α) :
    (tree.appendLeaves inputs).leaves = tree.leaves ++ inputs := by
  induction inputs generalizing tree with
  | nil => simp [Tree.appendLeaves]
  | cons input inputs ih =>
    change ((Tree.fork tree (.leaf input)).appendLeaves inputs).leaves = _
    rw [ih]
    simp [Tree.leaves, List.append_assoc]

theorem leftTree_admissible (space : IndexSpace) (order : space.Enumeration) :
    space.Admissible (space.leftTree order.val) :=
  ⟨order, leaves_appendLeaves (.leaf _) _⟩

private theorem eval_appendLeaves {α : Type u} {β : Type v} (value : α → β)
    (combine : β → β → β) (tree : Tree α) (inputs : List α) :
    (tree.appendLeaves inputs).eval value combine =
      inputs.foldl (fun acc input => combine acc (value input)) (tree.eval value combine) := by
  induction inputs generalizing tree with
  | nil => rfl
  | cons input inputs ih =>
    change ((Tree.fork tree (.leaf input)).appendLeaves inputs).eval value combine = _
    rw [ih]
    rfl

theorem eval_leftTree {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (order : List space.Trip) : reduction.eval space (space.leftTree order) =
      reduction.fold space order := by
  unfold Reduction.eval IndexSpace.leftTree Reduction.fold
  rw [eval_appendLeaves, List.foldl_map]
  rfl

private theorem foldl_leaves {α : Type u} {β : Type v} {combine : β → β → β}
    (assoc : Std.Associative combine) (value : α → β) (tree : Tree α) (initial : β) :
    tree.leaves.foldl (fun acc input => combine acc (value input)) initial =
      combine initial (tree.eval value combine) := by
  induction tree generalizing initial with
  | leaf input => rfl
  | fork left right ihLeft ihRight =>
    rw [Tree.leaves, List.foldl_append, ihLeft, ihRight, Tree.eval, assoc.assoc]

private theorem eval_eq_foldl {α : Type u} {β : Type v} {combine : β → β → β}
    (assoc : Std.Associative combine) (value : α → β) (tree : Tree α)
    {first : α} {rest : List α} (leaves : tree.leaves = first :: rest) :
    tree.eval value combine =
      rest.foldl (fun acc input => combine acc (value input)) (value first) := by
  induction tree generalizing first rest with
  | leaf input => cases leaves; rfl
  | fork left right ihLeft _ =>
    cases leftLeaves : left.leaves with
    | nil => exact (leaves_ne_nil left leftLeaves).elim
    | cons head tail =>
      change left.leaves ++ right.leaves = first :: rest at leaves
      rw [leftLeaves, List.cons_append] at leaves
      obtain ⟨rfl, rfl⟩ := List.cons.inj leaves
      rw [List.foldl_append, foldl_leaves assoc, ← ihLeft leftLeaves]
      rfl

theorem eval_eq_fold {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) (order : List space.Trip)
    (leaves : tree.leaves = Input.initial :: order.map Input.trip)
    (assoc : Std.Associative reduction.combine) :
    reduction.eval space tree = reduction.fold space order := by
  unfold Reduction.eval Reduction.fold
  rw [eval_eq_foldl assoc _ _ leaves, List.foldl_map]
  rfl

theorem fold_eq_denote {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (order : space.Enumeration) (assoc : Std.Associative reduction.combine)
    (comm : Std.Commutative reduction.combine) :
    reduction.fold space order.val = reduction.denote space := by
  unfold Reduction.fold Reduction.denote
  apply order.property.foldl_eq'
  intro first _ second _ acc
  rw [assoc.assoc, assoc.assoc, comm.comm (reduction.contribution (space.index first))]

theorem eval_eq_denote {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) (valid : space.Admissible tree)
    (assoc : Std.Associative reduction.combine) (comm : Std.Commutative reduction.combine) :
    reduction.eval space tree = reduction.denote space := by
  obtain ⟨order, leaves⟩ := valid
  exact (eval_eq_fold reduction space tree order.val leaves assoc).trans
    (fold_eq_denote reduction space order assoc comm)

theorem returns_denote {α : Type u} (reduction : Reduction α) (space : IndexSpace) :
    reduction.Returns space (reduction.denote space) :=
  ⟨space.leftTree space.trips, leftTree_admissible space ⟨space.trips, .refl _⟩,
    eval_leftTree reduction space space.trips⟩

theorem returns_iff_eq_denote {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (result : α) (assoc : Std.Associative reduction.combine)
    (comm : Std.Commutative reduction.combine) :
    reduction.Returns space result ↔ result = reduction.denote space := by
  constructor
  · rintro ⟨tree, valid, rfl⟩
    exact eval_eq_denote reduction space tree valid assoc comm
  · rintro rfl
    exact returns_denote reduction space

private theorem eq_leaf_of_leaves {α : Type u} (tree : Tree α) {input : α}
    (leaves : tree.leaves = [input]) : tree = .leaf input := by
  cases tree with
  | leaf other => cases leaves; rfl
  | fork left right =>
    have leftPos := List.length_pos_iff.mpr (leaves_ne_nil left)
    have rightPos := List.length_pos_iff.mpr (leaves_ne_nil right)
    have length := congrArg List.length leaves
    simp only [Tree.leaves, List.length_append, List.length_cons, List.length_nil] at length
    omega

private theorem trips_eq_nil (space : IndexSpace) (empty : space.upper ≤ space.lower) :
    space.trips = [] :=
  List.length_eq_zero_iff.mp (List.length_finRange.trans ((tripCount_eq_zero space).mpr empty))

theorem denote_of_empty {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (empty : space.upper ≤ space.lower) : reduction.denote space = reduction.initial := by
  unfold Reduction.denote Reduction.fold
  rw [trips_eq_nil space empty]
  rfl

theorem eval_of_empty {α : Type u} (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) (valid : space.Admissible tree) (empty : space.upper ≤ space.lower) :
    reduction.eval space tree = reduction.initial := by
  obtain ⟨⟨order, perm⟩, leaves⟩ := valid
  change order.Perm space.trips at perm
  change tree.leaves = Input.initial :: order.map Input.trip at leaves
  rw [trips_eq_nil space empty] at perm
  rw [perm.eq_nil, List.map_nil] at leaves
  rw [eq_leaf_of_leaves tree leaves]
  rfl

theorem grouped_eval_eq_denote {n : Nat} {Carrier : Fin n → Type u}
    (group : GroupedReduction Carrier) (space : IndexSpace) (tree : Tree (Input space))
    (valid : space.Admissible tree)
    (assoc : ∀ slot, Std.Associative (group.combine slot))
    (comm : ∀ slot, Std.Commutative (group.combine slot)) :
    group.toReduction.eval space tree = group.toReduction.denote space := by
  have groupAssoc : Std.Associative group.toReduction.combine :=
    ⟨fun first second third => funext fun slot => (assoc slot).assoc _ _ _⟩
  have groupComm : Std.Commutative group.toReduction.combine :=
    ⟨fun first second => funext fun slot => (comm slot).comm (first slot) (second slot)⟩
  exact eval_eq_denote group.toReduction space tree valid groupAssoc groupComm

private def twoTrips : IndexSpace := ⟨1, 5, 3, by decide⟩
private def firstTrip : twoTrips.Trip := ⟨0, by decide⟩
private def secondTrip : twoTrips.Trip := ⟨1, by decide⟩
private def lastContribution : Reduction Nat := ⟨99, id, fun _ next => next⟩

theorem order_sensitive :
    let space : IndexSpace := ⟨1, 5, 3, by decide⟩
    let reduction : Reduction Nat := ⟨99, id, fun _ next => next⟩
    Std.Associative reduction.combine ∧ reduction.Returns space 1 ∧ reduction.Returns space 4 := by
  change Std.Associative lastContribution.combine ∧
    lastContribution.Returns twoTrips 1 ∧ lastContribution.Returns twoTrips 4
  have ascending : twoTrips.trips = [firstTrip, secondTrip] := by decide
  let reverseOrder : twoTrips.Enumeration := ⟨[secondTrip, firstTrip], by
    rw [ascending]
    exact List.Perm.swap firstTrip secondTrip []⟩
  refine ⟨⟨fun _ _ _ => rfl⟩, ?_, returns_denote _ _⟩
  exact ⟨twoTrips.leftTree reverseOrder.val, leftTree_admissible twoTrips reverseOrder, rfl⟩

end Silmaril.MLIR.SCF.Parallel.Proofs
