module

public import Silmaril.Formats.SExp.Arena.Defs
import Mathlib.Data.Finset.Card

public section

namespace Silmaril.Proofs.Formats.SExp.Arena

open Silmaril.Formats (SExp2)
open Silmaril.Formats.SExpArena

variable {Ix Atom : Type*} {source target : Arena Ix Atom} {exports : List Ix}
variable {index : Ix} {expr expr' : SExp2 Atom}

theorem unfolds_unique (first : source.Unfolds index expr) (second : source.Unfolds index expr') :
    expr = expr' := by
  induction first generalizing expr' with
  | nil read =>
    cases second with
    | nil => rfl
    | atom other | cons other => rw [read] at other; cases other
  | atom read =>
    cases second with
    | nil other | cons other => rw [read] at other; cases other
    | atom other =>
      rw [read] at other
      cases other
      rfl
  | cons read _ _ ihCar ihCdr =>
    cases second with
    | nil other | atom other => rw [read] at other; cases other
    | cons other car cdr =>
      rw [read] at other
      cases other
      exact congrArg₂ SExp2.cons (ihCar car) (ihCdr cdr)

theorem pointed_denotation_eq_singleton {point : Pointed Ix Atom}
    (unfolded : point.arena.Unfolds point.index expr) : point.denotation = {expr} := by
  ext other
  rw [Set.mem_singleton_iff]
  exact ⟨fun h => unfolds_unique h unfolded, fun h => h.symm ▸ unfolded⟩

theorem unfolds_nil_iff : source.Unfolds index .nil ↔ source index = some .nil :=
  ⟨fun h => by cases h with | nil read => exact read, .nil⟩

theorem unfolds_atom_iff {value : Atom} :
    source.Unfolds index (.atom value) ↔ source index = some (.atom value) :=
  ⟨fun h => by cases h with | atom read => exact read, .atom⟩

theorem unfolds_cons_iff {car cdr : SExp2 Atom} :
    source.Unfolds index (.cons car cdr) ↔
      ∃ pair, source index = some (.cons pair) ∧
        source.Unfolds pair.car car ∧ source.Unfolds pair.cdr cdr := by
  constructor
  · intro unfolded
    cases unfolded with | cons read left right => exact ⟨_, read, left, right⟩
  · rintro ⟨pair, read, left, right⟩
    exact .cons read left right

theorem reachableFrom_child {parent child : Ix}
    (reached : source.ReachableFrom exports parent) (edge : source.Edge parent child) :
    source.ReachableFrom exports child := by
  obtain ⟨root, member, path⟩ := reached
  exact ⟨root, member, path.tail edge⟩

theorem unfolds_reindexes {Jx : Type*} {dest : Arena Jx Atom} {rename : Ix → Jx}
    (agrees : source.Reindexes dest exports rename) (reached : source.ReachableFrom exports index) :
    dest.Unfolds (rename index) expr ↔ source.Unfolds index expr := by
  induction expr generalizing index with
  | nil =>
    rw [unfolds_nil_iff, unfolds_nil_iff, agrees _ reached]
    cases source index with
    | none => simp
    | some cell => cases cell <;> simp [Cell.mapIndices]
  | atom value =>
    rw [unfolds_atom_iff, unfolds_atom_iff, agrees _ reached]
    cases source index with
    | none => simp
    | some cell => cases cell <;> simp [Cell.mapIndices]
  | cons car cdr ihCar ihCdr =>
    rw [unfolds_cons_iff, unfolds_cons_iff, agrees _ reached]
    cases read : source index with
    | none => simp
    | some cell =>
      cases cell with
      | nil | atom => simp [Cell.mapIndices]
      | cons pair =>
        have carReached := reachableFrom_child reached ⟨pair, read, Or.inl rfl⟩
        have cdrReached := reachableFrom_child reached ⟨pair, read, Or.inr rfl⟩
        simpa [Cell.mapIndices] using and_congr (ihCar carReached) (ihCdr cdrReached)

theorem exportDenotation_reindexes {Jx : Type*} {dest : Arena Jx Atom} {rename : Ix → Jx}
    (agrees : source.Reindexes dest exports rename) :
    dest.exportDenotation (exports.map rename) = source.exportDenotation exports := by
  ext expr
  change (∃ j ∈ exports.map rename, dest.Unfolds j expr) ↔
    (∃ i ∈ exports, source.Unfolds i expr)
  constructor
  · rintro ⟨j, member, unfolded⟩
    obtain ⟨i, original, rfl⟩ := List.mem_map.mp member
    exact ⟨i, original, (unfolds_reindexes agrees ⟨i, original, .refl⟩).mp unfolded⟩
  · rintro ⟨i, member, unfolded⟩
    exact ⟨rename i, List.mem_map_of_mem member,
      (unfolds_reindexes agrees ⟨i, member, .refl⟩).mpr unfolded⟩

theorem reindexes_id (preserves : source.PreservesReachable target exports) :
    source.Reindexes target exports id := by
  intro index reached
  change target index = (source index).map (Cell.mapIndices id)
  rw [preserves index reached]
  cases source index with
  | none => rfl
  | some cell => cases cell <;> rfl

private theorem unfolds_accessible (unfolded : source.Unfolds index expr) :
    Acc (fun child parent => source.Edge parent child) index := by
  induction unfolded with
  | nil read | atom read =>
    refine .intro _ ?_
    rintro _ ⟨_, other, _⟩
    rw [read] at other
    cases other
  | cons read _ _ ihCar ihCdr =>
    refine .intro _ ?_
    rintro _ ⟨_, other, same⟩
    rw [read] at other
    cases other
    rcases same with rfl | rfl
    · exact ihCar
    · exact ihCdr

private theorem acc_no_self {rel : Ix → Ix → Prop} (accessible : Acc rel index) :
    ¬ rel index index := by
  induction accessible with
  | intro _ _ ih => intro self; exact ih _ self self

theorem unfolds_acyclicBelow (unfolded : source.Unfolds index expr) : source.AcyclicBelow index := by
  rintro ⟨cycle, reached, loop⟩
  have accessible : Acc (fun child parent => source.Edge parent child) cycle := by
    clear loop
    have initial := unfolds_accessible unfolded
    induction reached with
    | refl => exact initial
    | tail _ edge ih => exact ih.inv edge
  exact acc_no_self accessible.transGen (Relation.transGen_swap.mpr loop)

private theorem unfolds_reachable_lookup {other : Ix} (unfolded : source.Unfolds index expr)
    (reached : source.Reachable index other) : ∃ cell, source other = some cell := by
  induction unfolded with
  | nil read | atom read =>
    rcases Relation.ReflTransGen.cases_head reached with rfl | ⟨_, ⟨_, edgeRead, _⟩, _⟩
    · exact ⟨_, read⟩
    · rw [read] at edgeRead
      cases edgeRead
  | cons read _ _ ihCar ihCdr =>
    rcases Relation.ReflTransGen.cases_head reached with rfl | ⟨_, ⟨_, edgeRead, child⟩, path⟩
    · exact ⟨_, read⟩
    · rw [read] at edgeRead
      cases edgeRead
      rcases child with rfl | rfl
      · exact ihCar path
      · exact ihCdr path

private theorem exists_unfolds_of_finite_reachable (keys : Finset Ix) :
    ∀ root, source.AcyclicBelow root →
      (∀ i, source.Reachable root i → i ∈ keys) →
      (∀ i, source.Reachable root i → ∃ cell, source i = some cell) →
      ∃ expr, source.Unfolds root expr := by
  classical
  induction keys using Finset.eraseInduction
  rename_i keys ih
  intro root acyclic covered occupied
  obtain ⟨cell, read⟩ := occupied root .refl
  cases cell with
  | nil => exact ⟨_, .nil read⟩
  | atom => exact ⟨_, .atom read⟩
  | cons pair =>
    have unfoldChild (child : Ix) (edge : source.Edge root child) :
        ∃ expr, source.Unfolds child expr := by
      refine ih root (covered root .refl) child ?_ ?_ ?_
      · rintro ⟨cycle, path, loop⟩
        exact acyclic ⟨cycle, Relation.ReflTransGen.head edge path, loop⟩
      · intro i path
        refine Finset.mem_erase.mpr ⟨?_, covered i (Relation.ReflTransGen.head edge path)⟩
        intro equal
        exact acyclic ⟨root, .refl, Relation.TransGen.head' edge (equal ▸ path)⟩
      · intro i path
        exact occupied i (Relation.ReflTransGen.head edge path)
    obtain ⟨car, carUnfolds⟩ := unfoldChild pair.car ⟨pair, read, Or.inl rfl⟩
    obtain ⟨cdr, cdrUnfolds⟩ := unfoldChild pair.cdr ⟨pair, read, Or.inr rfl⟩
    exact ⟨.cons car cdr, .cons read carUnfolds cdrUnfolds⟩

theorem exists_unfolds_iff (storage : FiniteLookup Ix (Cell Ix Atom)) (root : Ix) :
    (∃ expr, Arena.Unfolds storage.lookup root expr) ↔
      Arena.AcyclicBelow storage.lookup root ∧
        ∀ i, Arena.Reachable storage.lookup root i → ∃ cell, storage.lookup i = some cell := by
  constructor
  · rintro ⟨_, unfolded⟩
    exact ⟨unfolds_acyclicBelow unfolded, fun _ => unfolds_reachable_lookup unfolded⟩
  · rintro ⟨acyclic, occupied⟩
    refine exists_unfolds_of_finite_reachable storage.keys root acyclic (fun i reached => ?_) occupied
    by_contra outside
    obtain ⟨_, read⟩ := occupied i reached
    rw [storage.none_of_not_mem i outside] at read
    cases read

theorem markSweep_normalize_lookup {Entry : Type*} [CellEncoding Entry Ix Atom]
    (storage : FiniteLookup Ix Entry) (exports : List Ix) :
    (storage.markSweep exports).normalize.lookup = Arena.markSweep storage.normalize.lookup exports := by
  funext i
  classical
  change (if Arena.ReachableFrom storage.normalize.lookup exports i then storage.lookup i
    else none).bind CellEncoding.decode =
      if Arena.ReachableFrom storage.normalize.lookup exports i then storage.normalize.lookup i else none
  by_cases kept : Arena.ReachableFrom storage.normalize.lookup exports i <;> simp [kept]
  rfl

theorem erase_withRefCounts [DecidableEq Ix] (storage : FiniteLookup Ix (Cell Ix Atom)) :
    storage.withRefCounts.erase = storage := by
  cases storage with
  | mk keys lookup supported =>
    simp only [FiniteLookup.withRefCounts, RefCounted.erase, FiniteLookup.mapEntries,
      FiniteLookup.mk.injEq, true_and]
    funext index
    change ((lookup index).bind (fun cell => some (cell, _))).bind (fun entry => some entry.1) =
      lookup index
    cases lookup index <;> rfl

theorem withRefCounts_correct [DecidableEq Ix] (storage : FiniteLookup Ix (Cell Ix Atom)) :
    storage.withRefCounts.CountsCorrect := by
  intro index count h
  rw [erase_withRefCounts]
  change ((storage.lookup index).bind (fun cell => some (cell, _))).map Prod.snd = some count at h
  cases found : storage.lookup index <;> simp [found] at h
  exact h.symm

end Silmaril.Proofs.Formats.SExp.Arena
