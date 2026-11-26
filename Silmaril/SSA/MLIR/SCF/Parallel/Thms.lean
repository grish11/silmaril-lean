module

public import Silmaril.SSA.MLIR.SCF.Parallel.Defs
import Silmaril.Proofs.SSA.MLIR.SCF.Parallel.Reduction

public section

namespace Silmaril.MLIR.SCF.Parallel

universe u

/-- Exactly the ordinals below the trip count give induction values below the upper bound. -/
theorem IndexSpace.rank_lt_tripCount (space : IndexSpace) (rank : Nat) :
    rank < space.tripCount ↔ space.lower + rank * space.step < space.upper :=
  Proofs.rank_lt_tripCount space rank

theorem IndexSpace.tripCount_eq_zero (space : IndexSpace) :
    space.tripCount = 0 ↔ space.upper ≤ space.lower :=
  Proofs.tripCount_eq_zero space

theorem IndexSpace.lower_le_index (space : IndexSpace) (trip : space.Trip) :
    space.lower ≤ space.index trip :=
  Nat.le_add_right _ _

theorem IndexSpace.index_lt_upper (space : IndexSpace) (trip : space.Trip) :
    space.index trip < space.upper :=
  (space.rank_lt_tripCount trip.val).mp trip.isLt

theorem IndexSpace.upper_le_exitIndex (space : IndexSpace) :
    space.upper ≤ space.exitIndex := by
  apply Nat.le_of_not_gt
  intro below
  exact (Nat.lt_irrefl _) ((space.rank_lt_tripCount _).mpr below)

theorem IndexSpace.index_injective (space : IndexSpace) :
    ∀ {first second : space.Trip}, space.index first = space.index second → first = second :=
  Proofs.index_injective space

theorem IndexSpace.Enumeration.mem {space : IndexSpace} (order : space.Enumeration)
    (trip : space.Trip) : trip ∈ order.val :=
  order.property.mem_iff.mpr (List.mem_finRange trip)

theorem IndexSpace.Enumeration.nodup {space : IndexSpace} (order : space.Enumeration) :
    order.val.Nodup :=
  Proofs.enumeration_nodup order

/-- Every admissible enumeration has a left-associated tree. -/
theorem IndexSpace.leftTree_admissible (space : IndexSpace) (order : space.Enumeration) :
    space.Admissible (space.leftTree order.val) :=
  Proofs.leftTree_admissible space order

variable {α : Type u}

/-- The left-associated tree computes the fold for its enumeration without algebraic laws. -/
theorem Reduction.eval_leftTree (reduction : Reduction α) (space : IndexSpace)
    (order : List space.Trip) :
    reduction.eval space (space.leftTree order) = reduction.fold space order :=
  Proofs.eval_leftTree reduction space order

/-- Associativity removes dependence on the binary shape while preserving the leaf order. -/
theorem Reduction.eval_eq_fold (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) (order : List space.Trip)
    (leaves : tree.leaves = Input.initial :: order.map Input.trip)
    (assoc : Std.Associative reduction.combine) :
    reduction.eval space tree = reduction.fold space order :=
  Proofs.eval_eq_fold reduction space tree order leaves assoc

/-- Associativity and commutativity remove dependence on the trip order. -/
theorem Reduction.fold_eq_denote (reduction : Reduction α) (space : IndexSpace)
    (order : space.Enumeration) (assoc : Std.Associative reduction.combine)
    (comm : Std.Commutative reduction.combine) :
    reduction.fold space order.val = reduction.denote space :=
  Proofs.fold_eq_denote reduction space order assoc comm

theorem Reduction.eval_eq_denote (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) (valid : space.Admissible tree)
    (assoc : Std.Associative reduction.combine) (comm : Std.Commutative reduction.combine) :
    reduction.eval space tree = reduction.denote space :=
  Proofs.eval_eq_denote reduction space tree valid assoc comm

/-- The reference denotation always gives one admissible result. -/
theorem Reduction.returns_denote (reduction : Reduction α) (space : IndexSpace) :
    reduction.Returns space (reduction.denote space) :=
  Proofs.returns_denote reduction space

/-- For a total associative and commutative combiner, the result relation is a singleton. -/
theorem Reduction.returns_iff_eq_denote (reduction : Reduction α) (space : IndexSpace)
    (result : α) (assoc : Std.Associative reduction.combine)
    (comm : Std.Commutative reduction.combine) :
    reduction.Returns space result ↔ result = reduction.denote space :=
  Proofs.returns_iff_eq_denote reduction space result assoc comm

theorem Reduction.denote_of_empty (reduction : Reduction α) (space : IndexSpace)
    (empty : space.upper ≤ space.lower) : reduction.denote space = reduction.initial :=
  Proofs.denote_of_empty reduction space empty

/-- With zero trips, any admissible tree returns the initial value. -/
theorem Reduction.eval_of_empty (reduction : Reduction α) (space : IndexSpace)
    (tree : Tree (Input space)) (valid : space.Admissible tree) (empty : space.upper ≤ space.lower) :
    reduction.eval space tree = reduction.initial :=
  Proofs.eval_of_empty reduction space tree valid empty

/-- Pointwise combiner laws give the same deterministic result for the whole group. -/
theorem GroupedReduction.eval_eq_denote {n : Nat} {Carrier : Fin n → Type u}
    (group : GroupedReduction Carrier) (space : IndexSpace) (tree : Tree (Input space))
    (valid : space.Admissible tree)
    (assoc : ∀ slot, Std.Associative (group.combine slot))
    (comm : ∀ slot, Std.Commutative (group.combine slot)) :
    group.toReduction.eval space tree = group.toReduction.denote space :=
  Proofs.grouped_eval_eq_denote group space tree valid assoc comm

/-- On indices `1, 4`, the associative right projection returns either index,
depending on the trip order. -/
theorem order_sensitive :
    let space : IndexSpace := ⟨1, 5, 3, by decide⟩
    let reduction : Reduction Nat := ⟨99, id, fun _ next => next⟩
    Std.Associative reduction.combine ∧ reduction.Returns space 1 ∧ reduction.Returns space 4 :=
  Proofs.order_sensitive

end Silmaril.MLIR.SCF.Parallel
