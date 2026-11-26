module

public import Silmaril.Semantics.BTree.Defs

public section

namespace Silmaril.Proofs.Semantics.BTree

open Silmaril.Semantics.BTree

variable {Key Value Child : Type} [LinearOrder Key]

theorem route_get (key : Key) (branch : Branch Key Child) :
    branch.children[(branch.route key).1]? = some (branch.route key).2 := by
  obtain ⟨fenced, rightmost⟩ := branch
  induction fenced with
  | nil => rfl
  | cons first rest ih =>
    by_cases eligible : key ≤ first.1
    · simp [Branch.children, Branch.route, List.findIdx_cons, eligible]
    · simpa [Branch.children, Branch.route, List.findIdx_cons, eligible] using ih

private structure Summary (entries : List (Key × Value)) (lookup : Key → Option Value)
    (lower upper : Option Key) : Prop where
  ordered : entries.Pairwise (fun left right => left.1 < right.1)
  bounded : ∀ entry ∈ entries, InRange lower upper entry.1
  lookup_eq : ∀ key, lookup key = entries.lookup key

private theorem branch_summary (entries : Child → List (Key × Value)) (lookup : Child → Key → Option Value)
    (valid : Option Key → Option Key → Child → Prop)
    (childSummary : ∀ lower upper child, valid lower upper child → Summary (entries child) (lookup child) lower upper)
    (upper : Option Key) (rightmost : Child) (lower : Option Key) (fenced : List (Key × Child))
    (ok : ValidChildren valid upper rightmost lower fenced) :
    Summary (fenced.flatMap (fun entry => entries entry.2) ++ entries rightmost)
      (fun key => lookup ((Branch.mk fenced rightmost).route key).2 key) lower upper := by
  induction fenced generalizing lower with
  | nil => exact childSummary lower upper rightmost ok
  | cons first rest ih =>
    obtain ⟨divider, child⟩ := first
    obtain ⟨aboveLower, belowUpper, childValid, restValid⟩ := ok
    have firstSummary := childSummary lower (some divider) child childValid
    have restSummary := ih (some divider) restValid
    rw [List.flatMap_cons, List.append_assoc]
    refine ⟨List.pairwise_append.mpr ⟨firstSummary.ordered, restSummary.ordered, ?_⟩, ?_, ?_⟩
    · intro left leftMem right rightMem
      exact lt_of_le_of_lt ((firstSummary.bounded left leftMem).2 divider rfl)
        ((restSummary.bounded right rightMem).1 divider rfl)
    · intro entry present
      rcases List.mem_append.mp present with firstMem | restMem
      · have inFirst := firstSummary.bounded entry firstMem
        exact ⟨inFirst.1, fun bound eq => (inFirst.2 divider rfl).trans (le_of_lt (belowUpper bound eq))⟩
      · have inRest := restSummary.bounded entry restMem
        exact ⟨fun bound eq => (aboveLower bound eq).trans (inRest.1 divider rfl), inRest.2⟩
    · intro key
      rw [List.lookup_append]
      by_cases eligible : key ≤ divider
      · have absent : (rest.flatMap (fun entry => entries entry.2) ++ entries rightmost).lookup key = none := by
          apply List.lookup_eq_none_iff.mpr
          intro entry present
          have above := (restSummary.bounded entry present).1 divider rfl
          simpa using ne_of_lt (lt_of_le_of_lt eligible above)
        simpa [Branch.route, List.findIdx_cons, eligible, absent, Option.or_none] using firstSummary.lookup_eq key
      · have absent : (entries child).lookup key = none := by
          apply List.lookup_eq_none_iff.mpr
          intro entry present
          have below := (firstSummary.bounded entry present).2 divider rfl
          simpa using ne_of_gt (lt_of_le_of_lt below (lt_of_not_ge eligible))
        simpa [Branch.route, List.findIdx_cons, eligible, absent] using restSummary.lookup_eq key

private theorem node_summary (height : Nat) (lower upper : Option Key) (node : Node Key Value height)
    (ok : Node.ValidWithin height lower upper node) :
    Summary (Node.entries height node) (fun key => Node.lookup? key height node) lower upper := by
  induction height generalizing lower upper with
  | zero => exact ⟨ok.1, ok.2, fun _ => rfl⟩
  | succ height ih =>
    exact branch_summary (Node.entries height) (fun child key => Node.lookup? key height child)
      (Node.ValidWithin height) ih upper node.rightmost lower node.fenced ok.2

theorem entries_ordered {height : Nat} {lower upper : Option Key} {node : Node Key Value height}
    (ok : Node.ValidWithin height lower upper node) :
    (Node.entries height node).Pairwise (fun left right => left.1 < right.1) :=
  (node_summary height lower upper node ok).ordered

theorem entries_inRange {height : Nat} {lower upper : Option Key} {node : Node Key Value height}
    (ok : Node.ValidWithin height lower upper node) {entry : Key × Value}
    (present : entry ∈ Node.entries height node) : InRange lower upper entry.1 :=
  (node_summary height lower upper node ok).bounded entry present

theorem lookup_eq_entries {height : Nat} {lower upper : Option Key} {node : Node Key Value height}
    (ok : Node.ValidWithin height lower upper node) (key : Key) :
    Node.lookup? key height node = (Node.entries height node).lookup key :=
  (node_summary height lower upper node ok).lookup_eq key

end Silmaril.Proofs.Semantics.BTree
