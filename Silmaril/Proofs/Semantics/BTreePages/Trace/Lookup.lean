module

public import Silmaril.Semantics.BTreePages.Trace.Defs
import Silmaril.Semantics.BTreePages.Thms
import Silmaril.Semantics.Page.Trace.Thms

public section
namespace Silmaril.Proofs.Semantics.BTreePages

open Silmaril.Semantics Silmaril.Semantics.BTree Silmaril.Semantics.BTreePages

universe u
variable {Key Value Id : Type} {Memory : Type u} [LinearOrder Key]
variable {layout : Layout Id} {tree : Tree Key Value}
variable {store : Page.Store Id (PageData Key Value Id) Memory} {memory final : Memory}

theorem lookupTraceFrom_spec (rep : Represents store layout tree memory) (key : Key)
    {position : Position} {subtree : Tree Key Value} (reached : atPath tree position = some subtree) :
    let reads := lookupTraceFrom key layout position subtree.height subtree.root
    Page.Program.Records (lookup key subtree.height (layout position)) reads.toTrace (subtree.lookup? key) ∧
      reads.Agrees store.access memory ∧
      ∀ entry ∈ reads, Footprint layout tree entry.1 := by
  obtain ⟨height, node⟩ := subtree
  induction height generalizing position with
  | zero =>
    have dataAt : pageAt layout tree position = some (encode layout position 0 node) := by
      simp [pageAt, reached]
    have headRead := Page.Store.access_read_iff.mpr (rep.2 _ _ dataAt)
    have headPage := mem_footprint_iff.mpr ⟨position, _, rfl, dataAt⟩
    refine ⟨?_, ?_, ?_⟩
    · exact .read .pure
    · simpa [lookupTraceFrom, ReadWrite.ReadTrace.Agrees] using headRead
    · simpa [lookupTraceFrom] using headPage
  | succ height ih =>
    have dataAt : pageAt layout tree position = some (encode layout position (height + 1) node) := by
      simp [pageAt, reached]
    have headRead := Page.Store.access_read_iff.mpr (rep.2 _ _ dataAt)
    have headPage := mem_footprint_iff.mpr ⟨position, _, rfl, dataAt⟩
    have childReached : atPath tree (position ++ [(node.route key).1]) =
        some ⟨height, (node.route key).2⟩ := by
      rw [atPath_append, reached]
      simp [atPath, Branch.route_get]
    obtain ⟨records, agrees, footprint⟩ := ih (node.route key).2 childReached
    refine ⟨?_, ?_, ?_⟩
    · rw [lookup, lookupStep, Page.Program.read, Page.Program.bind, Page.Program.bind]
      apply Page.Program.Records.read
      simpa only [Page.Program.bind, inspect_branch, Tree.lookup?, Node.lookup?, ReadWrite.ReadTrace.toTrace] using records
    · simpa only [lookupTraceFrom, ReadWrite.ReadTrace.Agrees, List.forall_mem_cons] using ⟨headRead, agrees⟩
    · simpa only [lookupTraceFrom, List.forall_mem_cons] using ⟨headPage, footprint⟩

theorem lookupTrace_spec (rep : Represents store layout tree memory) (key : Key) :
    Page.Program.Records (lookup key tree.height (layout [])) (lookupTrace key layout tree).toTrace
      (tree.lookup? key) ∧
      (lookupTrace key layout tree).Agrees store.access memory ∧
      ∀ entry ∈ lookupTrace key layout tree, Footprint layout tree entry.1 :=
  lookupTraceFrom_spec rep key rfl

theorem replays_represents_of_disjoint {trace : ReadWrite.Trace Id (PageData Key Value Id)}
    (rep : Represents store layout tree memory) (run : trace.Replays store.access memory final)
    (disjoint : ∀ page, Footprint layout tree page → ¬ trace.Defs page) :
    Represents store layout tree final :=
  (represents_congr (fun p inside => (run.frame store.access_frames (disjoint p inside)).symm)).mp rep

end Silmaril.Proofs.Semantics.BTreePages
