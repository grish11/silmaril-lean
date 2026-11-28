module

public import Silmaril.Formats.SExp.Arena.Defs
import Silmaril.Proofs.Formats.SExp.Arena.Basic

public section

namespace Silmaril.Formats.SExpArena

variable {Ix Jx Atom R : Type*}
variable {source target : Arena Ix Atom} {exports : List Ix}
variable {index : Ix} {expr expr' : SExp2 Atom}

namespace Arena

theorem unfolds_unique (first : source.Unfolds index expr) (second : source.Unfolds index expr') :
    expr = expr' :=
  Proofs.Formats.SExp.Arena.unfolds_unique first second

theorem unfolds_nil_iff : source.Unfolds index .nil ↔ source index = some .nil :=
  Proofs.Formats.SExp.Arena.unfolds_nil_iff

theorem unfolds_atom_iff {value : Atom} :
    source.Unfolds index (.atom value) ↔ source index = some (.atom value) :=
  Proofs.Formats.SExp.Arena.unfolds_atom_iff

theorem unfolds_cons_iff {car cdr : SExp2 Atom} :
    source.Unfolds index (.cons car cdr) ↔
      ∃ pair, source index = some (.cons pair) ∧
        source.Unfolds pair.car car ∧ source.Unfolds pair.cdr cdr :=
  Proofs.Formats.SExp.Arena.unfolds_cons_iff

theorem not_unfolds_of_lookup_none (missing : source index = none) : ¬ source.Unfolds index expr := by
  intro unfolded
  cases unfolded <;> simp_all

theorem reachableFrom_root (member : index ∈ exports) : source.ReachableFrom exports index :=
  ⟨index, member, .refl⟩

theorem reachableFrom_child {parent child : Ix}
    (reached : source.ReachableFrom exports parent) (edge : source.Edge parent child) :
    source.ReachableFrom exports child :=
  Proofs.Formats.SExp.Arena.reachableFrom_child reached edge

theorem exportDenotation_eq_of_mem_iff {other : List Ix}
    (same : ∀ i, i ∈ exports ↔ i ∈ other) :
    source.exportDenotation exports = source.exportDenotation other := by
  ext expr
  exact ⟨fun ⟨i, member, h⟩ => ⟨i, (same i).mp member, h⟩,
    fun ⟨i, member, h⟩ => ⟨i, (same i).mpr member, h⟩⟩

theorem exportDenotation_perm {other : List Ix} (perm : exports.Perm other) :
    source.exportDenotation exports = source.exportDenotation other :=
  exportDenotation_eq_of_mem_iff fun _ => perm.mem_iff

theorem unfolds_reindexes {dest : Arena Jx Atom} {rename : Ix → Jx}
    (agrees : source.Reindexes dest exports rename) (reached : source.ReachableFrom exports index) :
    dest.Unfolds (rename index) expr ↔ source.Unfolds index expr :=
  Proofs.Formats.SExp.Arena.unfolds_reindexes agrees reached

/-- Compare compaction or renaming even across different index types. -/
theorem exportDenotation_reindexes {dest : Arena Jx Atom} {rename : Ix → Jx}
    (agrees : source.Reindexes dest exports rename) :
    dest.exportDenotation (exports.map rename) = source.exportDenotation exports :=
  Proofs.Formats.SExp.Arena.exportDenotation_reindexes agrees

/-- Agreement also preserves failure to unfold at a reachable index. -/
theorem unfolds_preservesReachable (preserves : source.PreservesReachable target exports)
    (reached : source.ReachableFrom exports index) :
    target.Unfolds index expr ↔ source.Unfolds index expr :=
  unfolds_reindexes (Proofs.Formats.SExp.Arena.reindexes_id preserves) reached

theorem restrict_preservesReachable {keep : Ix → Prop} [DecidablePred keep]
    (covers : ∀ i, source.ReachableFrom exports i → keep i) :
    source.PreservesReachable (source.restrict keep) exports :=
  fun i reached => ite_eq_left (covers i reached)

theorem exportDenotation_preservesReachable (preserves : source.PreservesReachable target exports) :
    target.exportDenotation exports = source.exportDenotation exports := by
  simpa using exportDenotation_reindexes (Proofs.Formats.SExp.Arena.reindexes_id preserves)

theorem markSweep_preservesReachable :
    source.PreservesReachable (source.markSweep exports) exports :=
  fun _ reached => ite_eq_left reached

theorem markSweep_lookup_unreachable (outside : ¬ source.ReachableFrom exports index) :
    source.markSweep exports index = none :=
  ite_eq_right outside

theorem exportDenotation_markSweep :
    (source.markSweep exports).exportDenotation exports = source.exportDenotation exports :=
  exportDenotation_preservesReachable markSweep_preservesReachable

theorem unfolds_acyclicBelow (unfolded : source.Unfolds index expr) : source.AcyclicBelow index :=
  Proofs.Formats.SExp.Arena.unfolds_acyclicBelow unfolded

end Arena

namespace Pointed

@[simp] theorem toExports_denotation (point : Pointed Ix Atom) :
    point.toExports.denotation = point.denotation := by
  ext expr
  change (∃ i ∈ [point.index], point.arena.Unfolds i expr) ↔ point.arena.Unfolds point.index expr
  simp

theorem toExports_equiv_iff {left right : Pointed Ix Atom} :
    left.toExports ≈ right.toExports ↔ left ≈ right := by
  change left.toExports.denotation = right.toExports.denotation ↔ left.denotation = right.denotation
  simp

theorem denotation_eq_singleton {point : Pointed Ix Atom}
    (unfolded : point.arena.Unfolds point.index expr) : point.denotation = {expr} :=
  Proofs.Formats.SExp.Arena.pointed_denotation_eq_singleton unfolded

theorem denotation_eq_empty_iff {point : Pointed Ix Atom} :
    point.denotation = ∅ ↔ ¬ ∃ expr, point.arena.Unfolds point.index expr := by
  change point.denotation = ∅ ↔ ¬ point.denotation.Nonempty
  rw [Set.not_nonempty_iff_eq_empty]

/-- A pointed arena is equivalent to a successfully unfolded one exactly when
it unfolds to the same expression. -/
theorem equiv_iff_unfolds {left right : Pointed Ix Atom}
    (unfolded : left.arena.Unfolds left.index expr) :
    left ≈ right ↔ right.arena.Unfolds right.index expr := by
  change left.denotation = right.denotation ↔ expr ∈ right.denotation
  rw [denotation_eq_singleton unfolded]
  exact ⟨fun h => h ▸ Set.mem_singleton expr, fun h => (denotation_eq_singleton h).symm⟩

end Pointed

namespace Rooted

theorem equiv_preservesReachable [Root R Ix] {rooted : Rooted Ix Atom R}
    (preserves : rooted.arena.PreservesReachable target (Root.indices rooted.roots)) :
    (⟨rooted.roots, target⟩ : Rooted Ix Atom R) ≈ rooted :=
  Arena.exportDenotation_preservesReachable preserves

theorem equiv_of_perm [Root R Ix] {left right : R}
    (perm : (Root.indices left).Perm (Root.indices right)) :
    (⟨left, source⟩ : Rooted Ix Atom R) ≈ (⟨right, source⟩ : Rooted Ix Atom R) :=
  Arena.exportDenotation_perm perm

theorem markSweep_equiv [Root R Ix] (rooted : Rooted Ix Atom R) : rooted.markSweep ≈ rooted :=
  Arena.exportDenotation_markSweep

end Rooted

namespace FiniteLookup

/-- A root in finite storage unfolds exactly when it reaches neither a cycle nor a missing lookup. -/
theorem exists_unfolds_iff (storage : FiniteLookup Ix (Cell Ix Atom)) (root : Ix) :
    (∃ expr, Arena.Unfolds storage.lookup root expr) ↔
      Arena.AcyclicBelow storage.lookup root ∧
        ∀ i, Arena.Reachable storage.lookup root i → ∃ cell, storage.lookup i = some cell :=
  Proofs.Formats.SExp.Arena.exists_unfolds_iff storage root

theorem ofList_normalize_lookup {Entry : Type*} [CellEncoding Entry Nat Atom] (entries : List Entry) :
    (ofList entries).normalize.lookup = Arena.ofList entries :=
  rfl

theorem markSweep_normalize_lookup {Entry : Type*} [CellEncoding Entry Ix Atom]
    (storage : FiniteLookup Ix Entry) (exports : List Ix) :
    (storage.markSweep exports).normalize.lookup = Arena.markSweep storage.normalize.lookup exports :=
  Proofs.Formats.SExp.Arena.markSweep_normalize_lookup storage exports

end FiniteLookup

namespace RefCounted

@[simp] theorem erase_withRefCounts [DecidableEq Ix] (storage : FiniteLookup Ix (Cell Ix Atom)) :
    storage.withRefCounts.erase = storage :=
  Proofs.Formats.SExp.Arena.erase_withRefCounts storage

theorem withRefCounts_correct [DecidableEq Ix] (storage : FiniteLookup Ix (Cell Ix Atom)) :
    storage.withRefCounts.CountsCorrect :=
  Proofs.Formats.SExp.Arena.withRefCounts_correct storage

end RefCounted

end Silmaril.Formats.SExpArena
