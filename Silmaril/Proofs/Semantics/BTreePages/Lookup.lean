module

public import Silmaril.Semantics.BTreePages.Defs
import Silmaril.Semantics.BTree.Thms
import Silmaril.Proofs.Semantics.BTreePages.Representation

public section
namespace Silmaril.Proofs.Semantics.BTreePages

open Silmaril.Semantics Silmaril.Semantics.BTree Silmaril.Semantics.BTreePages

universe u
variable {Key Value Id : Type} {Memory : Type u}
variable {M : Page.Model Id (PageData Key Value Id) Memory} {memory : Memory}
variable {layout : Layout Id} {tree : Tree Key Value}

theorem inspect_branch [LinearOrder Key] (layout : Layout Id) (position : Position) (height : Nat)
    (node : Node Key Value (height + 1)) (key : Key) :
    inspect key (encode layout position (height + 1) node) =
      .inr (layout (position ++ [(node.route key).1])) := by
  have zipIndex : node.fenced.zipIdx.findIdx (fun entry => decide (key ≤ entry.1.1)) =
      node.fenced.findIdx (fun entry => decide (key ≤ entry.1)) := by
    simpa only [List.zipIdx_map_fst, Function.comp_def] using
      (List.findIdx_map node.fenced.zipIdx Prod.fst (fun entry => decide (key ≤ entry.1))).symm
  simp only [encode, inspect, Branch.route, List.findIdx_map, Function.comp_def, zipIndex,
    List.getElem?_map, List.getElem?_zipIdx]
  generalize index : node.fenced.findIdx (fun entry => decide (key ≤ entry.1)) = slot
  cases found : node.fenced[slot]? with
  | some _ => simp
  | none =>
    have atEnd : slot = node.fenced.length :=
      Nat.le_antisymm (index ▸ List.findIdx_le_length) (List.getElem?_eq_none_iff.mp found)
    simp [atEnd]

private theorem run_read_call_iff {α : Type} {page : Id} {data : PageData Key Value Id}
    {next : Page.Reply (.read (Content := PageData Key Value Id) page) →
      Page.Program Id (PageData Key Value Id) α}
    {edits : List (Page.Edit Id (PageData Key Value Id))} {out : Page.Exit Id Memory α}
    (defined : M.store.lookup memory page = .defined data) :
    Page.Run M (.call (.read page) next) memory edits out ↔
      Page.Run M (next (.value data)) memory edits out := by
  constructor
  · intro run
    cases run with
    | call step rest =>
      cases step with
      | readDefined found =>
        rw [defined] at found
        cases Page.Slot.defined.inj found
        exact rest
    | ub step =>
      cases step with
      | readAbsent absent => rw [defined] at absent; cases absent
      | readUndef undef => rw [defined] at undef; cases undef
  · intro run
    exact .call (.readDefined defined) run

private theorem run_pure_iff {α : Type} {value : α}
    {edits : List (Page.Edit Id (PageData Key Value Id))} {out : Page.Exit Id Memory α} :
    Page.Run M (.pure value) memory edits out ↔ edits = [] ∧ out = .returned value memory := by
  constructor
  · rintro ⟨⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .pure

variable [LinearOrder Key]

theorem lookupStep_run_iff {page : Id} {data : PageData Key Value Id}
    {edits : List (Page.Edit Id (PageData Key Value Id))} {out : Page.Exit Id Memory (Option Value ⊕ Id)}
    (defined : M.store.lookup memory page = .defined data) (key : Key) :
    Page.Run M (lookupStep key page) memory edits out ↔
      edits = [] ∧ out = .returned (inspect key data) memory := by
  unfold lookupStep Page.Program.read
  rw [Page.Program.bind, run_read_call_iff defined]
  exact run_pure_iff

theorem lookup_subtree_run_iff (rep : Represents M.store layout tree memory) (key : Key)
    {position : Position} {subtree : Tree Key Value} (reached : atPath tree position = some subtree)
    {edits : List (Page.Edit Id (PageData Key Value Id))} {out : Page.Exit Id Memory (Option Value)} :
    Page.Run M (lookup key subtree.height (layout position)) memory edits out ↔
      edits = [] ∧ out = .returned (subtree.lookup? key) memory := by
  obtain ⟨height, node⟩ := subtree
  induction height generalizing position with
  | zero =>
    have read := rep.2 position (encode layout position 0 node) (by simp [pageAt, reached])
    rw [lookup, lookupStep, Page.Program.read, Page.Program.bind, Page.Program.bind, run_read_call_iff read]
    exact run_pure_iff
  | succ height ih =>
    have read := rep.2 position (encode layout position (height + 1) node) (by simp [pageAt, reached])
    have childReached : atPath tree (position ++ [(node.route key).1]) =
        some ⟨height, (node.route key).2⟩ := by
      rw [atPath_append, reached]
      simp [atPath, Branch.route_get]
    rw [lookup, lookupStep, Page.Program.read, Page.Program.bind, Page.Program.bind, run_read_call_iff read]
    simp only [Page.Program.bind, inspect_branch]
    exact ih _ childReached

end Silmaril.Proofs.Semantics.BTreePages
