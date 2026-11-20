module

public import Silmaril.Formats.Dasl.Measure.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Measure

open Silmaril.Formats.Dasl

variable {Name Ref : Type}

private theorem empty_valid : ({} : Metrics).Valid := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

private theorem parent_valid {link : Nat} (isLink : link ≤ 1) {children : Metrics} (valid : children.Valid) :
    (Metrics.parent link children).Valid := by
  obtain ⟨depth, links, linkDepth, path⟩ := valid
  constructor <;> simp only [Metrics.parent] <;> omega

private theorem sum_valid (children : List Metrics) (valid : ∀ child ∈ children, Metrics.Valid child) :
    (Metrics.sum children).Valid := by
  induction children with
  | nil => exact empty_valid
  | cons head tail ih =>
    have ⟨leftDepth, leftLinks, leftLinkDepth, leftPath⟩ := valid head (List.mem_cons_self ..)
    have ⟨rightDepth, rightLinks, rightLinkDepth, rightPath⟩ := ih (fun child hit => valid child (List.mem_cons_of_mem _ hit))
    change (Metrics.siblings head (Metrics.sum tail)).Valid
    constructor <;> simp only [Metrics.siblings] <;> omega

theorem measure_valid (scope : Scope) (tree : Tree Ref Name) : (tree.measure scope).Valid := by
  induction tree with
  | obj _ _ ih =>
    cases scope
    · exact parent_valid (Nat.le_refl 1) empty_valid
    · exact parent_valid (Nat.le_refl 1) ih
  | dict keys values ih =>
    apply parent_valid (Nat.zero_le 1)
    apply sum_valid
    intro child hit
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hit
    exact ih ⟨key.val, (Finset.mem_sort _).mp key.property⟩
  | list len values ih =>
    apply parent_valid (Nat.zero_le 1)
    apply sum_valid
    intro child hit
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hit
    exact ih index
  | ref | blob => exact parent_valid (Nat.le_refl 1) empty_valid
  | _ => exact parent_valid (Nat.zero_le 1) empty_valid

theorem mem_occurrences_iff (tree : Partial Name) (block : Block Name) :
    block ∈ tree.blockOccurrences ↔ block.BoundIn tree.bindings := by
  induction tree with
  | ref | blob | i64 | bytes | string | bool | null =>
    cases block <;> simp [Partial.blockOccurrences, Partial.bindings, Block.BoundIn]
  | obj name child ih =>
    cases block <;> simp [Partial.blockOccurrences, Partial.bindings, Block.BoundIn, ih]
  | dict keys values ih =>
    simp only [Partial.blockOccurrences, List.mem_flatMap, List.mem_attach, true_and]
    cases block <;> simp only [Block.BoundIn, Partial.bindings]
    all_goals
      constructor
      · rintro ⟨key, hit⟩
        exact ⟨⟨key.val, (Finset.mem_sort _).mp key.property⟩, (ih _).mp hit⟩
      · rintro ⟨key, hit⟩
        exact ⟨⟨key.val, (Finset.mem_sort _).mpr key.property⟩, (ih _).mpr hit⟩
  | list len values ih =>
    simp only [Partial.blockOccurrences, List.mem_flatten, List.mem_ofFn]
    cases block <;> simp only [Partial.bindings, Block.BoundIn]
    all_goals
      constructor
      · rintro ⟨_, ⟨index, rfl⟩, hit⟩
        exact ⟨index, (ih index).mp hit⟩
      · rintro ⟨index, hit⟩
        exact ⟨_, ⟨index, rfl⟩, (ih index).mpr hit⟩

theorem blocks_bound {store : Store Name} {root : Name} {tree : Partial Name}
    (present : PartialNames store root tree) {block : Block Name} (hit : block ∈ tree.blocks root) :
    block.BoundIn store := by
  rcases List.mem_cons.mp hit with rfl | inside
  · exact present.1
  · have found := (mem_occurrences_iff tree block).mp inside
    cases block
    · exact present.2.1 found
    · exact present.2.2 found

theorem block_eq_of_same_link {store : Store Name} (bound : store.Binding) {left right : Block Name}
    (first : left.BoundIn store) (second : right.BoundIn store) (same : left.link = right.link) : left = right := by
  cases left <;> cases right <;> simp only [Block.link, Link.obj.injEq, Link.blob.injEq, reduceCtorEq] at same
  · cases same
    exact congrArg (Block.object _) (bound.1 first second)
  · cases same
    exact congrArg (Block.blob _) (bound.2 first second)

theorem inline_within_max {blocks : List (Block Name)} {block : Block Name} (hit : block ∈ blocks) :
    block.inlineMetrics.Within (maxInlineMetrics blocks) := by
  induction blocks with
  | nil => cases hit
  | cons head tail ih =>
    rcases List.mem_cons.mp hit with rfl | inside
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> exact Nat.le_max_left ..
    · obtain ⟨nodes, depth, links, linkDepth⟩ := ih inside
      exact ⟨nodes.trans (Nat.le_max_right ..), depth.trans (Nat.le_max_right ..),
        links.trans (Nat.le_max_right ..), linkDepth.trans (Nat.le_max_right ..)⟩

theorem bytes_within_max {serialize : Shallow Name → Option ByteArray} {blocks : List (Block Name)}
    {block : Block Name} (hit : block ∈ blocks) {limit : Nat} (checked : maxBlockBytes? serialize blocks = some limit) :
    ∃ bytes, block.byteSize? serialize = some bytes ∧ bytes ≤ limit := by
  induction blocks generalizing limit with
  | nil => cases hit
  | cons head tail ih =>
    cases first : head.byteSize? serialize with
    | none => simp [maxBlockBytes?, first] at checked
    | some size =>
      cases rest : tail.mapM (Block.byteSize? serialize) with
      | none => simp [maxBlockBytes?, first, rest] at checked
      | some sizes =>
        have same : max size (sizes.foldr max 0) = limit := by simpa [maxBlockBytes?, first, rest] using checked
        subst limit
        rcases List.mem_cons.mp hit with rfl | inside
        · exact ⟨size, first, Nat.le_max_left ..⟩
        · obtain ⟨bytes, read, bounded⟩ := ih inside (limit := sizes.foldr max 0) (by simp [maxBlockBytes?, rest])
          exact ⟨bytes, read, bounded.trans (Nat.le_max_right ..)⟩

end Silmaril.Proofs.Formats.Dasl.Measure
