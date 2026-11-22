module

public import Silmaril.Formats.Dasl.Prolly.Range.Defs
public import Silmaril.Semantics.OrderedMap.Operations.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyRange

open Silmaril.Formats.Dasl.Prolly (Fault)
open Silmaril.Formats.Dasl.Prolly.Range (Result includes selectedVisits selectedVisitsWith selectedChildren throughUpper scanWith)
open Silmaril.Formats.Dasl.Prolly.Range (intervalSubmap scanTwoSided)
open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} [LinearOrder Key]

private theorem mapM_sound {Item Output Error : Type} {items : List Item} {fetch : Item → Except Error Output}
    {truth : Item → Output} {results : List Output}
    (sound : ∀ item ∈ items, ∀ found, fetch item = .ok found → found = truth item)
    (checked : items.mapM fetch = .ok results) : results = items.map truth := by
  induction items generalizing results with
  | nil => exact (Except.ok.inj checked).symm
  | cons head tail ih =>
    cases first : fetch head with
    | error err => simp [List.mapM_cons, first, Bind.bind, Except.bind] at checked
    | ok item =>
      have correct := sound head (by simp) item first
      cases rest : tail.mapM fetch with
      | error err => simp [List.mapM_cons, first, rest, Bind.bind, Except.bind] at checked
      | ok items =>
        have tailCorrect := ih (fun next hit => sound next (List.mem_cons_of_mem _ hit)) rest
        simpa [List.mapM_cons, first, rest, Bind.bind, Except.bind, Pure.pure, Except.pure, correct, tailCorrect]
          using checked.symm

private theorem pruned_empty {lower upper separator : Key} {entries : List (Key × Payload)}
    (ordered : entries.Pairwise fun left right => left.1 < right.1)
    (maximum : entries.getLast?.map Prod.fst = some separator) (pruned : ¬ lower ≤ separator) :
    entries.filter (fun entry => includes lower upper entry.1) = [] := by
  obtain ⟨last, lastEq, sep⟩ := Option.map_eq_some_iff.mp maximum
  apply List.filter_eq_nil_iff.mpr
  intro entry present
  have weak : entries.Pairwise (fun left right => left.1 ≤ right.1) := ordered.imp le_of_lt
  have lastBound := weak.rel_getLast_of_rel_getLast_getLast
    present (le_refl (entries.getLast (List.ne_nil_of_mem present)).1)
  rw [List.getLast_of_getLast?_eq_some lastEq, sep] at lastBound
  simp [includes, not_le.mpr (lt_of_le_of_lt lastBound (lt_of_not_ge pruned))]

private theorem selected_map {Child Target : Type} (cutoff : Option Key) (children : List (Key × Child))
    (label : Key × Child → Key × Target) (preserves : ∀ child, (label child).1 = child.1) :
    selectedChildren cutoff (children.map label) = (selectedChildren cutoff children).map label := by
  cases cutoff with
  | none => rfl
  | some upper =>
    induction children with
    | nil => rfl
    | cons child rest ih =>
      change throughUpper upper ((child :: rest).map label) = (throughUpper upper (child :: rest)).map label
      simp only [List.map_cons, throughUpper, preserves]
      split
      · rfl
      · exact congrArg (List.cons (label child)) ih

private theorem selected_sublist {Child : Type} (cutoff : Option Key) (children : List (Key × Child)) :
    List.Sublist (selectedChildren cutoff children) children := by
  cases cutoff with
  | none => exact List.Sublist.refl _
  | some upper =>
    induction children with
    | nil => exact List.Sublist.refl _
    | cons child rest ih =>
      simp only [selectedChildren, Option.elim_some, throughUpper]
      apply List.Sublist.cons_cons
      split
      · exact List.nil_sublist _
      · exact ih

private theorem filter_throughUpper (lower upper : Key) (level : Nat) (node : Node Key Payload (level + 1))
    (ordered : (flatten (level + 1) node).Pairwise fun left right => left.1 < right.1)
    (maxima : ∀ child ∈ node, (flatten level child.2).getLast?.map Prod.fst = some child.1) :
    ((throughUpper upper node).flatMap (fun child => flatten level child.2)).filter (fun entry => includes lower upper entry.1) =
      (flatten (level + 1) node).filter (fun entry => includes lower upper entry.1) := by
  induction node with
  | nil => rfl
  | cons child rest ih =>
    have orderedParts := List.pairwise_append.mp (by
      simpa only [flatten, List.flatMap_cons] using ordered :
      (flatten level child.2 ++ rest.flatMap fun edge => flatten level edge.2).Pairwise fun left right => left.1 < right.1)
    by_cases stop : upper ≤ child.1
    · obtain ⟨last, found, key⟩ := Option.map_eq_some_iff.mp (maxima child (by simp))
      have tailEmpty : (rest.flatMap (fun edge => flatten level edge.2)).filter
          (fun entry => includes lower upper entry.1) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro entry member
        have larger := orderedParts.2.2 last (List.mem_of_getLast? found) entry member
        rw [key] at larger
        simp [includes, not_lt.mpr (stop.trans (le_of_lt larger))]
      simp [throughUpper, stop, flatten, List.filter_append, tailEmpty]
    · have tail := ih orderedParts.2.1 (fun edge member => maxima edge (List.mem_cons_of_mem _ member))
      simp [throughUpper, stop, flatten, List.filter_append, tail]

theorem range_scan_sound {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width : Nat) (lower upper : Key) (pruneUpper : Bool)
    (fuel level : Nat) (node : Node Key Payload level)
    (ordered : (flatten level node).Pairwise fun left right => left.1 < right.1)
    (separators : Node.Separators level node)
    (agrees : ∀ block ∈ blockOccurrences address level node,
      ∀ actual, read (address block) = .ok actual → actual = block)
    {expected : Option Nat} {result : Result Key Payload}
    (checked : scanWith read width lower upper pruneUpper fuel expected (address (nodeBlock address level node)) = .ok result) :
    result = ⟨(flatten level node).filter fun entry => includes lower upper entry.1,
      selectedVisitsWith lower (if pruneUpper then some upper else none) level node⟩ := by
  let cutoff := if pruneUpper then some upper else none
  induction fuel generalizing level expected result with
  | zero => simp [scanWith] at checked
  | succ fuel ih =>
    have root : nodeBlock address level node ∈ blockOccurrences address level node := by
      cases level <;> simp [blockOccurrences]
    cases seen : read (address (nodeBlock address level node)) with
    | error fault => simp [scanWith, seen, Bind.bind, Except.bind] at checked
    | ok actual =>
      have eq := agrees _ root actual seen
      subst actual
      simp only [scanWith, seen, Bind.bind, Except.bind] at checked
      cases level with
      | zero =>
        simp only [nodeBlock] at checked
        split at checked
        · exact (Except.ok.inj checked).symm
        · contradiction
      | succ level =>
        simp only [nodeBlock] at checked
        split at checked
        · rw [selected_map cutoff node (fun child => (child.1, address (nodeBlock address level child.2)))
            (fun _ => rfl)] at checked
          simp only [List.mapM_map, Nat.add_sub_cancel] at checked
          let picked := selectedChildren cutoff node
          let fetch := fun (child : Key × Node Key Payload level) =>
            if lower ≤ child.1 then scanWith read width lower upper pruneUpper fuel (some level)
              (address (nodeBlock address level child.2)) else .ok ⟨[], 0⟩
          change (picked.mapM fetch >>= fun groups =>
            .ok ⟨groups.flatMap Result.entries, 1 + (groups.map Result.visits).sum⟩) = .ok result at checked
          cases fetched : picked.mapM fetch with
          | error fault => simp [fetched, Bind.bind, Except.bind] at checked
          | ok groups =>
            let truth := fun (child : Key × Node Key Payload level) =>
              (⟨(flatten level child.2).filter fun entry => includes lower upper entry.1,
                if lower ≤ child.1 then selectedVisitsWith lower cutoff level child.2 else 0⟩ : Result Key Payload)
            have exactGroups : groups = picked.map truth := by
              apply mapM_sound (checked := fetched)
              intro child retained found foundChild
              have member := (selected_sublist cutoff node).mem retained
              have orderedChild := (List.pairwise_flatMap.mp ordered).1 child member
              by_cases selects : lower ≤ child.1
              · have exactChild := ih level child.2 orderedChild (separators.2 child member).2
                  (fun block observed actual hit => agrees block (List.mem_cons_of_mem _
                    (List.mem_flatMap.mpr ⟨child, member, observed⟩)) actual hit)
                  (by simpa [fetch, selects] using foundChild)
                simpa [truth, selects] using exactChild
              · have empty := pruned_empty orderedChild (separators.2 child member).1 (upper := upper) selects
                simpa [truth, fetch, selects, empty] using foundChild.symm
            have output : result = ⟨groups.flatMap Result.entries, 1 + (groups.map Result.visits).sum⟩ := by
              simpa [fetched, Bind.bind, Except.bind] using checked.symm
            rw [output, exactGroups]
            have unchanged : ((picked.flatMap fun child => flatten level child.2).filter
                (fun entry => includes lower upper entry.1)) =
                (flatten (level+1) node).filter (fun entry => includes lower upper entry.1) := by
              cases pruneUpper
              · rfl
              · exact filter_throughUpper lower upper level node ordered (fun child member => (separators.2 child member).1)
            simp only [List.flatMap_map, Function.comp_def, List.map_map, truth]
            rw [← List.filter_flatMap, unchanged]
            rfl
        · contradiction

theorem visits_le_all (address : Block Name Key Payload → Name) (lower : Key) (level : Nat)
    (node : Node Key Payload level) : selectedVisits lower level node ≤ (blockOccurrences address level node).length := by
  induction level with
  | zero => rfl
  | succ level ih =>
    simp only [selectedVisits, selectedVisitsWith, selectedChildren, Option.elim_none, blockOccurrences,
      List.length_cons, List.length_flatMap] at ih ⊢
    have sums : (node.map fun child => if lower ≤ child.1 then selectedVisitsWith lower none level child.2 else 0).sum ≤
        (node.map fun child => (blockOccurrences address level child.2).length).sum := by
      induction node with
      | nil => rfl
      | cons child rest tail =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (by split; exact ih _; exact Nat.zero_le _) tail
    omega

theorem visits_le_lower (lower upper : Key) (level : Nat) (node : Node Key Payload level) :
    selectedVisitsWith lower (some upper) level node ≤ selectedVisits lower level node := by
  induction level with
  | zero => rfl
  | succ level ih =>
    simp only [selectedVisits, selectedVisitsWith, selectedChildren, Option.elim_some, Option.elim_none]
    apply Nat.add_le_add_left
    induction node with
    | nil => rfl
    | cons child rest tail =>
      have here : (if lower ≤ child.1 then selectedVisitsWith lower (some upper) level child.2 else 0) ≤
          (if lower ≤ child.1 then selectedVisitsWith lower none level child.2 else 0) := by
        split <;> solve | exact ih child.2 | rfl
      simp only [throughUpper, List.map_cons, List.sum_cons]
      apply Nat.add_le_add here
      split
      · exact Nat.zero_le _
      · exact tail

theorem interval_submap [DecidableEq Payload]
    {left right : Name → Except (Fault Name) (Block Name Key Payload)} {leftRoot rightRoot : Name}
    {width fuel : Nat} {lower upper : Key} {leftSlice rightSlice : OrderedMap Key Payload}
    (exactLeft : ∀ result, scanTwoSided left width lower upper fuel none leftRoot = .ok result →
      result.entries = leftSlice.entries)
    (exactRight : ∀ result, scanTwoSided right width lower upper fuel none rightRoot = .ok result →
      result.entries = rightSlice.entries)
    {result : Bool} (checked : intervalSubmap left right width fuel lower upper leftRoot rightRoot = .ok result) :
    result = leftSlice.submap rightSlice := by
  cases leftScan : scanTwoSided left width lower upper fuel none leftRoot with
  | error err => simp [intervalSubmap, leftScan, bind, Except.bind] at checked
  | ok leftOut =>
    cases rightScan : scanTwoSided right width lower upper fuel none rightRoot with
    | error err => simp [intervalSubmap, leftScan, rightScan, bind, Except.bind] at checked
    | ok rightOut =>
      unfold OrderedMap.submap OrderedMap.lookup?
      simpa [intervalSubmap, leftScan, rightScan, bind, Except.bind, pure, Except.pure,
        exactLeft leftOut leftScan, exactRight rightOut rightScan] using checked.symm

end Silmaril.Proofs.Formats.Dasl.ProllyRange
