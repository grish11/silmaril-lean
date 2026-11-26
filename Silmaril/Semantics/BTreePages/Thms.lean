module

public import Silmaril.Semantics.BTreePages.Defs
public import Silmaril.Semantics.BTree.Thms
import Silmaril.Proofs.Semantics.BTreePages.Lookup
import Silmaril.Proofs.Semantics.BTreePages.Representation

public section
namespace Silmaril.Semantics.BTreePages

open BTree

universe u
variable {Key Value Id : Type} {Memory : Type u}
variable {layout : Layout Id} {tree : Tree Key Value}
variable {store : Page.Store Id (PageData Key Value Id) Memory} {memory other : Memory}
variable {M : Page.Model Id (PageData Key Value Id) Memory}

theorem atPath_append (tree : Tree Key Value) (start suffix : Position) :
    atPath tree (start ++ suffix) = (atPath tree start).bind (atPath · suffix) :=
  Proofs.Semantics.BTreePages.atPath_append tree start suffix

theorem mem_footprint_iff {page : Id} :
    Footprint layout tree page ↔
      ∃ position data, layout position = page ∧ pageAt layout tree position = some data :=
  Proofs.Semantics.BTreePages.mem_footprint_iff

theorem compatible_of_disjoint {left right : Tree Key Value} {leftLayout rightLayout : Layout Id}
    (disjoint : ∀ page, Footprint leftLayout left page → ¬ Footprint rightLayout right page) :
    Compatible leftLayout rightLayout left right := by
  intro p q a b hp hq eq
  exact (disjoint _ (mem_footprint_iff.mpr ⟨p, a, rfl, hp⟩) (mem_footprint_iff.mpr ⟨q, b, eq.symm, hq⟩)).elim

variable [LinearOrder Key]

/-- The representation set depends only on the ordinary slots in its footprint. -/
theorem represents_congr (agree : AgreesOn store (Footprint layout tree) memory other) :
    Represents store layout tree memory ↔ Represents store layout tree other :=
  Proofs.Semantics.BTreePages.represents_congr agree

/-- A point update to any slot outside the footprint preserves representation. -/
theorem represents_set_outside {page : Id} (outside : ¬ Footprint layout tree page)
    (value : Page.Slot (PageData Key Value Id)) :
    Represents store layout tree (store.set memory page value) ↔ Represents store layout tree memory :=
  Proofs.Semantics.BTreePages.represents_set_outside outside value

/-- Every well-formed layout has a representative over arbitrary outside slots. -/
theorem represents_over [DecidableEq Id] (ok : WellFormed layout tree)
    (outside : Page.MapMemory Id (PageData Key Value Id)) :
    ∃ memory, Represents (Page.mapStore Id _) layout tree memory ∧
      AgreesOn (Page.mapStore Id _) (fun page => ¬ Footprint layout tree page) memory outside :=
  Proofs.Semantics.BTreePages.represents_over ok outside

/-- Well-formed roots have a common representative exactly when they require
identical payloads at shared addresses. Disjoint footprints are always compatible. -/
theorem shared_representation_iff [DecidableEq Id] {left right : Tree Key Value}
    {leftLayout rightLayout : Layout Id} (leftOK : WellFormed leftLayout left)
    (rightOK : WellFormed rightLayout right) (outside : Page.MapMemory Id (PageData Key Value Id)) :
    (∃ memory, Represents (Page.mapStore Id _) leftLayout left memory ∧
      Represents (Page.mapStore Id _) rightLayout right memory ∧
      AgreesOn (Page.mapStore Id _)
        (fun page => ¬ Footprint leftLayout left page ∧ ¬ Footprint rightLayout right page) memory outside) ↔
      Compatible leftLayout rightLayout left right :=
  Proofs.Semantics.BTreePages.shared_representation_iff leftOK rightOK outside

/-- Encoded pointers preserve the slot selected by the abstract router. -/
theorem inspect_branch (layout : Layout Id) (position : Position) (height : Nat)
    (node : Node Key Value (height + 1)) (key : Key) :
    inspect key (encode layout position (height + 1) node) =
      .inr (layout (position ++ [(node.route key).1])) :=
  Proofs.Semantics.BTreePages.inspect_branch layout position height node key

/-- The one-page operation returns the pure decision with no effects on a defined slot. -/
theorem lookupStep_run_iff {page : Id} {data : PageData Key Value Id}
    {edits : List (Page.Edit Id (PageData Key Value Id))} {out : Page.Exit Id Memory (Option Value ⊕ Id)}
    (defined : M.store.lookup memory page = .defined data) (key : Key) :
    Page.Run M (lookupStep key page) memory edits out ↔
      edits = [] ∧ out = .returned (inspect key data) memory :=
  Proofs.Semantics.BTreePages.lookupStep_run_iff defined key

variable {edits : List (Page.Edit Id (PageData Key Value Id))} {out : Page.Exit Id Memory (Option Value)}

/-- From any reachable subtree, the program has exactly one outcome. It returns
the abstract result (including a miss), keeps the whole memory, and emits no edits. -/
theorem lookup_subtree_run_iff (rep : Represents M.store layout tree memory) (key : Key)
    {position : Position} {subtree : Tree Key Value} (reached : atPath tree position = some subtree) :
    Page.Run M (lookup key subtree.height (layout position)) memory edits out ↔
      edits = [] ∧ out = .returned (subtree.lookup? key) memory :=
  Proofs.Semantics.BTreePages.lookup_subtree_run_iff rep key reached

theorem lookup_run_iff (rep : Represents M.store layout tree memory) (key : Key) :
    Page.Run M (lookup key tree.height (layout [])) memory edits out ↔
      edits = [] ∧ out = .returned (tree.lookup? key) memory :=
  lookup_subtree_run_iff rep key rfl

/-- On a represented tree the operational result is also the ordered-map lookup. -/
theorem lookup_orderedMap_run_iff (rep : Represents M.store layout tree memory) (key : Key) :
    Page.Run M (lookup key tree.height (layout [])) memory edits out ↔
      edits = [] ∧ out = .returned ((tree.toOrderedMap rep.1.1).lookup? key) memory := by
  rw [lookup_run_iff rep, tree.lookup_eq_orderedMap rep.1.1]

/-- Replacing slots outside the footprint preserves the result, and execution
returns the entire replacement memory unchanged. -/
theorem lookup_frame (rep : Represents M.store layout tree memory)
    (agree : AgreesOn M.store (Footprint layout tree) memory other) (key : Key) :
    Page.Run M (lookup key tree.height (layout [])) other edits out ↔
      edits = [] ∧ out = .returned (tree.lookup? key) other :=
  lookup_run_iff ((represents_congr agree).mp rep) key

/-- Changes confined to a disjoint footprint leave lookup unchanged. -/
theorem lookup_frame_of_disjoint {otherTree : Tree Key Value} {otherLayout : Layout Id}
    (rep : Represents M.store layout tree memory)
    (disjoint : ∀ page, Footprint layout tree page → ¬ Footprint otherLayout otherTree page)
    (agree : AgreesOn M.store (fun page => ¬ Footprint otherLayout otherTree page) memory other)
    (key : Key) :
    Page.Run M (lookup key tree.height (layout [])) other edits out ↔
      edits = [] ∧ out = .returned (tree.lookup? key) other :=
  lookup_frame rep (fun page inside => agree page (disjoint page inside)) key

/-- Reading one of two represented roots preserves the other, including when
both roots observe some of the same slots. -/
theorem shared_lookup_preserves {otherTree : Tree Key Value} {otherLayout : Layout Id} {final : Memory}
    {result : Option Value} (rep : Represents M.store layout tree memory)
    (shared : Represents M.store otherLayout otherTree memory) (key : Key)
    (run : Page.Run M (lookup key tree.height (layout [])) memory edits (.returned result final)) :
    Represents M.store otherLayout otherTree final := by
  have ⟨_, rfl⟩ := Page.Exit.returned.inj ((lookup_run_iff rep key).mp run).2
  exact shared

end Silmaril.Semantics.BTreePages
