module

public import Silmaril.Formats.Dasl.Prolly.Route.Defs
public import Silmaril.Semantics.Prolly.Routing.Thms
import Mathlib.Data.List.Pairwise

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyRouteComplete

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics.Prolly

variable {Name Key Payload Child : Type} [LinearOrder Key]

private theorem ordered_separators (children : List (Key × Child)) (entries : Child → List (Key × Payload))
    (ordered : (children.flatMap (entries ∘ Prod.snd)).Pairwise fun left right => left.1 < right.1)
    (maxima : ∀ child ∈ children, (entries child.2).getLast?.map Prod.fst = some child.1) :
    children.Pairwise (fun left right => left.1 < right.1) := by
  induction children with
  | nil => exact .nil
  | cons first rest ih =>
    simp only [List.flatMap_cons, Function.comp_apply, List.pairwise_append] at ordered
    refine .cons (fun child hit => ?_) (ih ordered.2.1 fun child hit => maxima child (by simp [hit]))
    have firstMax := maxima first (by simp)
    have childMax := maxima child (by simp [hit])
    obtain ⟨firstLast, firstEq, firstKey⟩ := Option.map_eq_some_iff.mp firstMax
    obtain ⟨childLast, childEq, childKey⟩ := Option.map_eq_some_iff.mp childMax
    obtain ⟨firstInit, firstList⟩ := List.getLast?_eq_some_iff.mp firstEq
    obtain ⟨childInit, childList⟩ := List.getLast?_eq_some_iff.mp childEq
    simpa only [firstKey, childKey] using ordered.2.2 firstLast (by simp [firstList]) childLast
      (List.mem_flatMap.mpr ⟨child, hit, by simp [childList]⟩)

theorem route_complete {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width : Nat) (key : Key) (level : Nat)
    (node : Node Key Payload level) (bounded : Node.Bounded width level node)
    (ordered : (flatten level node).Pairwise fun left right => left.1 < right.1)
    (separators : Node.Separators level node) (reads : PathReads read address key level node)
    {fuel : Nat} (enough : level < fuel) {expected : Option Nat}
    (expectedLevel : expected = none ∨ expected = some level) :
    route read width key fuel expected (address (nodeBlock address level node)) =
      .ok ((flatten level node).lookup key) := by
  induction level generalizing fuel expected with
  | zero =>
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ enough).elim
    | succ fuel =>
      simp only [PathReads, nodeBlock] at reads
      have valid : (expected = none ∨ expected = some 0) ∧ node.length ≤ width ∧
          node.Pairwise (fun left right => left.1 < right.1) := ⟨expectedLevel, bounded, ordered⟩
      simp only [nodeBlock, flatten, route, reads, Bind.bind, Except.bind, ite_eq_left valid]
  | succ level ih =>
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ enough).elim
    | succ fuel =>
      have maxima := fun child hit => (separators.2 child hit).1
      have branchOrder := ordered_separators node (flatten level) ordered maxima
      have lookupEq := lookup_children key node (flatten level) ordered maxima
      change (flatten (level + 1) node).lookup key = _ at lookupEq
      let locate := fun (child : Key × Node Key Payload level) =>
        (child.1, address (nodeBlock address level child.2))
      have mapped : selectChild key (node.map locate) = (selectChild key node).map locate := by
        simp [selectChild, locate, Function.comp_def]
      have mapOrder : (node.map locate).Pairwise (fun left right => left.1 < right.1) :=
        List.pairwise_map.mpr branchOrder
      have positive : 0 < node.length := List.length_pos_iff.mpr separators.1
      have valid : (expected = none ∨ expected = some (level + 1)) ∧ 0 < level + 1 ∧
          0 < (node.map locate).length ∧ (node.map locate).length ≤ width ∧
          (node.map locate).Pairwise (fun left right => left.1 < right.1) :=
        ⟨expectedLevel, Nat.zero_lt_succ _, by simpa using positive, by simpa using bounded.1, mapOrder⟩
      have hit := reads.1
      change read (address (.branch (level + 1) (node.map locate))) = .ok (.branch (level + 1) (node.map locate)) at hit
      change route read width key (fuel + 1) expected (address (.branch (level + 1) (node.map locate))) = _
      simp only [route, hit, Bind.bind, Except.bind, ite_eq_left valid, mapped, lookupEq, Nat.add_sub_cancel]
      cases next : selectChild key node with
      | none => rfl
      | some child =>
        have childHit : child ∈ node := List.mem_of_find?_eq_some (by simpa only [selectChild] using next)
        have sub : List.Sublist (flatten level child.2) (flatten (level + 1) node) :=
          List.sublist_flatten_of_mem (List.mem_map.mpr ⟨child, childHit, rfl⟩)
        exact ih child.2 (bounded.2 child childHit) (ordered.sublist sub) (separators.2 child childHit).2
          (reads.2 child next) (Nat.lt_of_succ_lt_succ enough) (.inr rfl)

private theorem pathReads_of_all {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (key : Key) (level : Nat) (node : Node Key Payload level)
    (all : ∀ block ∈ blockOccurrences address level node, read (address block) = .ok block) :
    PathReads read address key level node := by
  induction level with
  | zero => exact all _ (by simp [blockOccurrences])
  | succ level ih =>
    refine ⟨all _ (by simp [blockOccurrences]), fun child next => ?_⟩
    have hit : child ∈ node := List.mem_of_find?_eq_some (by simpa only [selectChild] using next)
    exact ih child.2 fun block present => all _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, hit, present⟩))

theorem stored_pathReads {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {address : Block Name Key Payload → Name} {tree : Semantics.Prolly.Tree Key Payload} {store : Store Name}
    (stored : Stored codec address tree store) {read : Read Name}
    (readsAll : ∀ ⦃name value⦄, store.objects name value → read name = .found value) (key : Key) :
    PathReads (readBlock codec read) address key tree.level tree.root := by
  apply pathReads_of_all
  intro block hit
  obtain ⟨value, encoded, present⟩ := stored block hit
  simp [readBlock, readsAll present, codec.recovers encoded]

end Silmaril.Proofs.Formats.Dasl.ProllyRouteComplete
