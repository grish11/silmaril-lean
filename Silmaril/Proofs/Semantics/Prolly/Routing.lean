module

public import Silmaril.Semantics.Prolly.Routing.Defs
public import Silmaril.Semantics.Prolly.Thms
import Mathlib.Data.List.Pairwise

public section

namespace Silmaril.Proofs.Semantics.Prolly.Routing

open Silmaril.Semantics.Prolly

variable {Key Payload Child : Type}

private theorem last_leaf (level : Nat) {node : Node Key Payload level} (valid : Node.Separators level node)
    {last : Key × Content Key Payload level} (atEnd : node.getLast? = some last) :
    (flatten level node).getLast?.map Prod.fst = some last.1 := by
  cases level with
  | zero => simp [flatten, atEnd]
  | succ level =>
    obtain ⟨initial, eq⟩ := List.getLast?_eq_some_iff.mp atEnd
    have hit : last ∈ node := by simp [eq]
    obtain ⟨leaf, lastEq, keyEq⟩ := Option.map_eq_some_iff.mp (valid.2 last hit).1
    simp [eq, flatten, List.flatMap_append, lastEq, keyEq]

private theorem lift_separators (level : Nat) {node : Node Key Payload level} (valid : Node.Separators level node)
    (nonempty : node ≠ []) (groups : List (Node Key Payload level)) (grouped : groups.flatten = node) :
    Node.Separators (level + 1) (lift groups) := by
  constructor
  · intro empty
    have keyEq := last_leaf level valid (List.getLast?_eq_some_getLast nonempty)
    have flatNonempty : flatten level node ≠ [] := by intro flatEmpty; simp [flatEmpty] at keyEq
    exact flatNonempty (by rw [← grouped, ← lift_entries, empty]; rfl)
  · intro child hit
    obtain ⟨group, groupHit, eq⟩ := List.mem_filterMap.mp hit
    cases group with
    | nil => simp at eq
    | cons first rest =>
      cases eq
      have included : ∀ item ∈ first :: rest, item ∈ node := fun item inside =>
        grouped ▸ List.mem_flatten.mpr ⟨_, groupHit, inside⟩
      have childValid : Node.Separators level (first :: rest) := by
        cases level with
        | zero => trivial
        | succ level => exact ⟨List.cons_ne_nil _ _, fun item inside => valid.2 item (included item inside)⟩
      exact ⟨last_leaf level childValid (by simp [List.getLast?_cons]), childValid⟩

private theorem grow_separators (policy : Policy Key) (fuel level : Nat) (node : Node Key Payload level)
    (valid : Node.Separators level node) :
    Node.Separators (grow policy fuel level node).level (grow policy fuel level node).root := by
  induction fuel generalizing level with
  | zero => exact valid
  | succ fuel ih =>
    let groups := chunk (fun count (pair : Key × Content Key Payload level) => policy.cut level count pair.1) node
    let property := fun tree : Tree Key Payload => Node.Separators tree.level tree.root
    by_cases fits : node.length ≤ policy.width
    · have eq : grow policy (fuel + 1) level node = ⟨level, node⟩ := by simp [grow, fits]
      exact (congrArg property eq).mpr valid
    · have eq : grow policy (fuel + 1) level node = grow policy fuel (level + 1) (lift groups) := by
        simp [grow, fits, groups]
      exact (congrArg property eq).mpr (ih (level + 1) _
        (lift_separators level valid (fun empty => fits (by simp [empty])) groups (flatten_chunk _ _)))

theorem build_routable [LinearOrder Key] (policy : Policy Key) (map : Silmaril.Semantics.OrderedMap Key Payload) :
    (build policy map).Routable :=
  ⟨by simpa using map.ordered, grow_separators policy map.entries.length 0 map.entries trivial⟩

theorem lookup_children [LinearOrder Key] (key : Key) (children : List (Key × Child)) (entries : Child → List (Key × Payload))
    (ordered : (children.flatMap (entries ∘ Prod.snd)).Pairwise fun left right => left.1 < right.1)
    (maxima : ∀ child ∈ children, (entries child.2).getLast?.map Prod.fst = some child.1) :
    (children.flatMap (entries ∘ Prod.snd)).lookup key =
      (selectChild key children).bind (fun child => (entries child.2).lookup key) := by
  induction children with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, Function.comp_apply, List.lookup_append, selectChild, List.find?_cons]
    have ⟨headOrder, tailOrder, across⟩ := List.pairwise_append.mp ordered
    obtain ⟨last, lastEq, sep⟩ := Option.map_eq_some_iff.mp (maxima head (by simp))
    have lastIn : last ∈ entries head.2 := by
      obtain ⟨initial, eq⟩ := List.getLast?_eq_some_iff.mp lastEq
      simp [eq]
    by_cases eligible : key ≤ head.1
    · have absent : (tail.flatMap (entries ∘ Prod.snd)).lookup key = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry present
        have above : head.1 < entry.1 := sep ▸ across last lastIn entry present
        simpa using (ne_of_lt (lt_of_le_of_lt eligible above))
      simp [eligible, absent, Option.or_none]
    · have absent : (entries head.2).lookup key = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry present
        have weak : (entries head.2).Pairwise (fun left right => left.1 ≤ right.1) :=
          headOrder.imp (fun less => le_of_lt less)
        have lastBound := weak.rel_getLast_of_rel_getLast_getLast
          present (le_refl ((entries head.2).getLast (List.ne_nil_of_mem present)).1)
        rw [List.getLast_of_getLast?_eq_some lastEq, sep] at lastBound
        simpa using (ne_of_gt (lt_of_le_of_lt lastBound (lt_of_not_ge eligible)))
      have tailMax : ∀ child ∈ tail, (entries child.2).getLast?.map Prod.fst = some child.1 :=
        fun child hit => maxima child (List.mem_cons_of_mem _ hit)
      simpa [selectChild, eligible, absent] using ih tailOrder tailMax

end Silmaril.Proofs.Semantics.Prolly.Routing
