module

public import Silmaril.Semantics.BTreePages.Trace.Defs
public import Silmaril.Semantics.BTreePages.Thms
public import Silmaril.Semantics.Page.Array.Thms
import Silmaril.Proofs.Semantics.BTreePages.Trace.Lookup

public section
namespace Silmaril.Semantics.BTreePages

open BTree

universe u
variable {Key Value Id : Type} {Memory : Type u} [LinearOrder Key]
variable {layout : Layout Id} {tree : Tree Key Value}
variable {store : Page.Store Id (PageData Key Value Id) Memory} {memory final : Memory}

/-- The logical route records the actual read replies of a represented lookup.
It agrees with the starting store and stays inside the tree's footprint. -/
theorem lookupTrace_spec (rep : Represents store layout tree memory) (key : Key) :
    Page.Program.Records (lookup key tree.height (layout [])) (lookupTrace key layout tree).toTrace
      (tree.lookup? key) ∧
      (lookupTrace key layout tree).Agrees store.access memory ∧
      ∀ entry ∈ lookupTrace key layout tree, Footprint layout tree entry.1 :=
  Proofs.Semantics.BTreePages.lookupTrace_spec rep key

theorem lookupTrace_replays (rep : Represents store layout tree memory) (key : Key) :
    (lookupTrace key layout tree).toTrace.Replays store.access memory memory :=
  (ReadWrite.ReadTrace.replays_iff _).mpr ⟨rfl, (lookupTrace_spec rep key).2.1⟩

theorem replays_represents_of_disjoint {trace : ReadWrite.Trace Id (PageData Key Value Id)}
    (rep : Represents store layout tree memory) (run : trace.Replays store.access memory final)
    (disjoint : ∀ page, Footprint layout tree page → ¬ trace.Defs page) :
    Represents store layout tree final :=
  Proofs.Semantics.BTreePages.replays_represents_of_disjoint rep run disjoint

variable {n : Nat} {arrayLayout : Layout Nat} {arrayTree : Tree Key Value}

theorem lookupTrace_replays_undefArray {pages : Page.UndefArray n (PageData Key Value Nat)}
    (rep : RepresentsUndefArray arrayLayout arrayTree pages) (key : Key) :
    (lookupTrace key arrayLayout arrayTree).toTrace.Replays (Page.UndefArray.access n _) pages pages :=
  Page.UndefArray.replays_memory_iff.mp (lookupTrace_replays rep key)

theorem lookupTrace_replays_array {pages : Page.Array n (PageData Key Value Nat)}
    (rep : RepresentsArray arrayLayout arrayTree pages) (key : Key) :
    (lookupTrace key arrayLayout arrayTree).toTrace.Replays (Page.Array.access n _) pages pages :=
  Page.Array.replays_embed_iff.mp (lookupTrace_replays_undefArray rep key)

end Silmaril.Semantics.BTreePages
