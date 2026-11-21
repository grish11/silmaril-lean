module

public import Silmaril.Formats.Dasl.Mst.Build.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.MstBuild

open Silmaril.Formats.Dasl.Mst
open Silmaril.Semantics.Naming (Relation Subset)

variable {Name : Type}

theorem split_flatten (layerOf : Key → Nat) (layer : Nat) (records : List (Record Name)) :
    (splitLayer layerOf layer records).flatten = records := by
  induction records with
  | nil => rfl
  | cons record tail ih =>
    by_cases atLayer : layerOf record.1 = layer <;>
      simpa [splitLayer, atLayer, LayerSplit.flatten, List.cons_append, List.append_assoc] using
        congrArg (record :: ·) ih

theorem split_pivots (layerOf : Key → Nat) (layer : Nat) (records : List (Record Name)) :
    (splitLayer layerOf layer records).pivots.map Prod.fst = records.filter (fun record => layerOf record.1 == layer) := by
  induction records with
  | nil => rfl
  | cons record tail ih => by_cases atLayer : layerOf record.1 = layer <;> simp [splitLayer, atLayer, ih]

private def Below (layerOf : Key → Nat) (layer : Nat) (gap : List (Record Name)) : Prop :=
  ∀ record ∈ gap, layerOf record.1 < layer

private theorem split_gaps (layerOf : Key → Nat) (layer : Nat) {records : List (Record Name)}
    (leLayer : ∀ record ∈ records, layerOf record.1 ≤ layer) :
    Below layerOf layer (splitLayer layerOf layer records).left ∧
      ∀ pivot ∈ (splitLayer layerOf layer records).pivots, Below layerOf layer pivot.2 := by
  induction records with
  | nil => simp [splitLayer, Below]
  | cons record tail ih =>
    obtain ⟨left, right⟩ := ih (fun next mem => leLayer next (.tail _ mem))
    by_cases atLayer : layerOf record.1 = layer
    · simpa [splitLayer, atLayer] using And.intro (show Below layerOf layer ([] : List (Record Name)) by simp [Below]) (And.intro left right)
    · have below : layerOf record.1 < layer := Nat.lt_of_le_of_ne (leLayer record (.head _)) atLayer
      simp only [splitLayer, ite_eq_right atLayer]
      exact ⟨fun next mem => (List.mem_cons.mp mem).elim (fun eq => eq ▸ below) (left next), right⟩

theorem maxLayer_spec (layerOf : Key → Nat) (records : List (Record Name)) :
    (∀ record ∈ records, layerOf record.1 ≤ maxLayer layerOf records) ∧
      (records = [] ∨ ∃ record ∈ records, layerOf record.1 = maxLayer layerOf records) := by
  induction records with
  | nil => simp [maxLayer]
  | cons record tail ih =>
    simp only [maxLayer, List.foldr_cons] at ⊢
    change (_ ∧ (_ ∨ ∃ next ∈ record :: tail, layerOf next.1 = max (layerOf record.1) (maxLayer layerOf tail)))
    refine ⟨?_, Or.inr ?_⟩
    · intro next mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact Nat.le_max_left ..
      · exact (ih.1 _ mem).trans (Nat.le_max_right ..)
    · by_cases le : maxLayer layerOf tail ≤ layerOf record.1
      · exact ⟨record, .head _, (Nat.max_eq_left le).symm⟩
      · rcases ih.2 with rfl | ⟨next, mem, eq⟩
        · exact (le (Nat.zero_le _)).elim
        · exact ⟨next, .tail _ mem, eq.trans (Nat.max_eq_right (by omega)).symm⟩

private def ChildSound (layerOf : Key → Nat) (reference : Relation Name (Node Name))
    (parent : Nat) (descend : List (Record Name) → Option (Built Name)) : Prop :=
  ∀ ⦃gap child ctx⦄, gap ≠ [] → OrderedRecords gap → (∀ entry ∈ gap, ctx.Contains entry.1) →
    Below layerOf parent gap → ctx.layer = parent - 1 → ctx.root = false →
    descend gap = some child → Subset child.observed reference →
    Realizes layerOf reference (some ctx) child.root gap

private theorem gap_spec {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {parent : Nat} {descend : List (Record Name) → Option (Built Name)}
    (sound : ChildSound layerOf reference parent descend) {ctx : Context}
    (level : ctx.layer = parent - 1) (nonroot : ctx.root = false) {gap : List (Record Name)}
    (ordered : OrderedRecords gap) (within : ∀ entry ∈ gap, ctx.Contains entry.1) (below : Below layerOf parent gap)
    {side : Option Name × List (Name × Node Name)} (found : buildGap descend gap = some side)
    (included : ∀ pair ∈ side.2, reference pair.1 pair.2) :
    (side.1 = none ↔ gap = []) ∧ (parent = 0 → side.1 = none) ∧
      ∀ name, side.1 = some name → Realizes layerOf reference (some ctx) name gap := by
  cases gap with
  | nil => cases (Option.some.inj found); simp
  | cons head tail =>
    obtain ⟨child, built, eq⟩ := Option.map_eq_some_iff.mp found
    subst side
    refine ⟨by simp, ?_, ?_⟩
    · intro zero
      have low := below head (.head _)
      omega
    · intro name same
      cases (Option.some.inj same)
      exact sound (by simp) ordered within below level nonroot built (fun _ _ member => included _ member)

private structure Groups (layerOf : Key → Nat) (reference : Relation Name (Node Name))
    (ctx : Context) (node : Node Name) (records : List (Record Name)) : Prop where
  witness : ∃ groups : List (SlotEntries Name), groups.flatMap Prod.snd = records ∧
    groups.map Prod.fst = slotsFrom ctx node.left node.entries ∧
    (∀ group ∈ groups, ∀ entry ∈ group.2, group.1.Covers entry.1) ∧
    (∀ group ∈ groups, ∀ key record, group.1 = .record key record → group.2 = [(key, record)]) ∧
    (∀ group ∈ groups, ∀ next, group.1 = .gap next none → group.2 = []) ∧
    (∀ group ∈ groups, ∀ next child, group.1 = .gap next (some child) →
      Realizes layerOf reference (some next) child group.2)

private theorem prepend_gap {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {ctx : Context} {name : Option Name} {gap : List (Record Name)}
    (bounded : ∀ entry ∈ gap, ctx.Contains entry.1) (pruned : name = none → gap = [])
    (child : ∀ child, name = some child → Realizes layerOf reference (some ctx) child gap)
    {group : SlotEntries Name} (eq : group = (.gap ctx name, gap)) :
    (∀ entry ∈ group.2, group.1.Covers entry.1) ∧
    (∀ key record, group.1 = .record key record → group.2 = [(key, record)]) ∧
    (∀ next, group.1 = .gap next none → group.2 = []) ∧
    (∀ next name, group.1 = .gap next (some name) → Realizes layerOf reference (some next) name group.2) := by
  subst group
  refine ⟨bounded, by simp, ?_, ?_⟩
  · intro next same
    exact pruned (Slot.gap.inj same).2
  · intro next name same
    obtain ⟨rfl, hit⟩ := Slot.gap.inj same
    exact child _ hit

private theorem assemble_spec {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {parent : Nat} {descend : List (Record Name) → Option (Built Name)}
    (sound : ChildSound layerOf reference parent descend) {ctx : Context}
    (level : ctx.layer = parent - 1) (nonroot : ctx.root = false)
    {left : List (Record Name)} {pivots : List (Record Name × List (Record Name))}
    (ordered : OrderedRecords (LayerSplit.flatten ⟨left, pivots⟩))
    (within : ∀ entry ∈ LayerSplit.flatten ⟨left, pivots⟩, ctx.Contains entry.1)
    (belowLeft : Below layerOf parent left) (belowRight : ∀ pivot ∈ pivots, Below layerOf parent pivot.2)
    {result : Node Name × List (Name × Node Name)} (built : assemble descend left pivots = some result)
    (included : ∀ pair ∈ result.2, reference pair.1 pair.2) :
    (result.1.entries.map (fun entry => (entry.key, entry.record)) = pivots.map Prod.fst) ∧
    (result.1.left = none ↔ left = []) ∧
    (parent = 0 → result.1.left = none ∧ ∀ entry ∈ result.1.entries, entry.right = none) ∧
    Groups layerOf reference ctx result.1 (LayerSplit.flatten ⟨left, pivots⟩) := by
  induction pivots generalizing left ctx result with
  | nil =>
    obtain ⟨side, found, rfl⟩ := Option.map_eq_some_iff.mp built
    simp only [LayerSplit.flatten, List.flatMap_nil, List.append_nil] at ordered within ⊢
    obtain ⟨missing, dry, child⟩ := gap_spec sound level nonroot ordered within belowLeft found included
    have spec := prepend_gap (reference := reference) (layerOf := layerOf) within missing.mp child rfl
    refine ⟨rfl, missing, fun zero => ⟨dry zero, by simp⟩, ⟨[⟨.gap ctx side.1, left⟩], by simp, rfl, ?_, ?_, ?_, ?_⟩⟩
    all_goals intro group mem; rw [List.mem_singleton.mp mem]; first | exact spec.1 | exact spec.2.1 | exact spec.2.2.1 | exact spec.2.2.2
  | cons first rest ih =>
    rcases first with ⟨pivot, right⟩
    cases named : buildGap descend left <;> simp [assemble, named] at built
    rename_i side
    cases builtTail : assemble descend right rest <;> simp [builtTail] at built
    rename_i tail
    subst result
    let lowerCtx := {ctx with upper := some pivot.1}
    let upperCtx := {ctx with lower := some pivot.1}
    change OrderedRecords (left ++ pivot :: LayerSplit.flatten ⟨right, rest⟩) at ordered
    change (∀ entry ∈ left ++ pivot :: LayerSplit.flatten ⟨right, rest⟩, ctx.Contains entry.1) at within
    obtain ⟨ordLeft, ordRest, across⟩ := List.pairwise_append.mp ordered.1
    obtain ⟨higher, ordRight⟩ := List.pairwise_cons.mp ordRest
    have boundedLeft : ∀ entry ∈ left, lowerCtx.Contains entry.1 := fun entry mem =>
      ⟨(within _ (List.mem_append_left _ mem)).1, by simpa [lowerCtx] using across _ mem _ (.head _)⟩
    have boundedRight : ∀ entry ∈ LayerSplit.flatten ⟨right, rest⟩, upperCtx.Contains entry.1 := fun entry mem =>
      ⟨by simpa [upperCtx] using higher _ mem, (within _ (List.mem_append_right _ (.tail _ mem))).2⟩
    obtain ⟨missing, dry, child⟩ := gap_spec sound (ctx := lowerCtx) level nonroot
      ⟨ordLeft, fun entry mem => ordered.2 _ (List.mem_append_left _ mem)⟩ boundedLeft belowLeft named
      (fun pair mem => included pair (List.mem_append_left _ mem))
    obtain ⟨keys, _, dryTail, groups, flattened, slots, bounded, records, pruned, children⟩ :=
      ih (ctx := upperCtx) level nonroot ⟨ordRight, fun entry mem => ordered.2 _ (List.mem_append_right _ (.tail _ mem))⟩
        boundedRight (belowRight _ (.head _)) (fun pos mem => belowRight pos (.tail _ mem)) builtTail
        (fun pair mem => included pair (List.mem_append_right _ mem))
    refine ⟨by simp [keys], missing, ?_, ⟨(.gap lowerCtx side.1, left) :: (.record pivot.1 pivot.2, [pivot]) :: groups,
      ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro zero
      have noTail := dryTail zero
      exact ⟨dry zero, fun entry mem => (List.mem_cons.mp mem).elim (fun eq => eq ▸ noTail.1) (noTail.2 entry)⟩
    · simp [LayerSplit.flatten, flattened]
    · simp [slots, slotsFrom, lowerCtx, upperCtx]
    all_goals
      intro group mem
      rcases List.mem_cons.mp mem with rfl | mem
      · have spec := prepend_gap boundedLeft missing.mp child rfl
        first | exact spec.1 | exact spec.2.1 | exact spec.2.2.1 | exact spec.2.2.2
      · rcases List.mem_cons.mp mem with rfl | mem
        · simp [Slot.Covers]
        · first | exact bounded group mem | exact records group mem | exact pruned group mem | exact children group mem

private theorem assemble_valid {layerOf : Key → Nat} {ctx : Context} {records : List (Record Name)}
    {built : Node Name} (ordered : OrderedRecords records)
    (within : ∀ entry ∈ records, ctx.Contains entry.1)
    (rootLayer : ctx.root = true → ctx.layer = maxLayer layerOf records)
    (nonempty : ctx.root = false → records ≠ [])
    (keys : built.entries.map (fun entry => (entry.key, entry.record)) = records.filter (fun e => layerOf e.1 == ctx.layer))
    (missing : built.left = none ↔ (splitLayer layerOf ctx.layer records).left = [])
    (dry : ctx.layer = 0 → built.left = none ∧ ∀ entry ∈ built.entries, entry.right = none) :
    ctx.Valid layerOf built ∧ (ctx.root = true → (built.rootContext layerOf).layer = ctx.layer) := by
  have hits : ∀ entry ∈ built.entries, (entry.key, entry.record) ∈ records ∧ layerOf entry.key = ctx.layer := by
    intro entry mem
    have mapped := List.mem_map_of_mem (f := fun entry : Entry Name => (entry.key, entry.record)) mem
    rw [keys] at mapped
    simpa using mapped
  have noPivots (empty : built.entries = []) : (splitLayer layerOf ctx.layer records).pivots = [] := by
    apply (List.map_eq_nil_iff (f := Prod.fst)).mp
    rw [split_pivots, ← keys, empty]
    rfl
  have emptyRoot (root : ctx.root = true) (empty : built.entries = []) : records = [] := by
    rcases (maxLayer_spec layerOf records).2 with nil | ⟨entry, mem, eq⟩
    · exact nil
    · have chosen : entry ∈ records.filter (fun e => layerOf e.1 == ctx.layer) := by
        simp [mem, eq, rootLayer root]
      rw [← keys, empty] at chosen
      simp at chosen
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← List.pairwise_map (f := fun entry : Entry Name => (entry.key, entry.record))
      (R := fun left right => left.1.before right.1), keys]
    exact ordered.1.sublist List.filter_sublist
  · intro entry mem
    obtain ⟨known, layer⟩ := hits entry mem
    exact ⟨⟨ordered.2 _ known, layer, within _ known⟩, fun zero => by rw [(dry zero).2 entry mem]; rfl⟩
  · intro zero
    rw [(dry zero).1]
    rfl
  · intro empty
    have nil := List.isEmpty_iff.mp empty
    cases root : ctx.root
    · have present : built.left ≠ none := by
        intro absent
        apply nonempty root
        rw [← split_flatten layerOf ctx.layer records, LayerSplit.flatten, missing.mp absent, noPivots nil]
        rfl
      simpa [root, Option.isSome_iff_ne_none] using present
    · have zero : ctx.layer = 0 := by rw [rootLayer root, emptyRoot root nil]; rfl
      simp [zero, (dry zero).1]
  · intro root
    cases entries : built.entries with
    | nil => simp [Node.rootContext, entries, rootLayer root, emptyRoot root entries, maxLayer]
    | cons first tail =>
      have mem : first ∈ built.entries := entries ▸ .head _
      simpa [Node.rootContext, entries] using (hits first mem).2

private theorem buildAt_realizes {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    {reference : Relation Name (Node Name)} {layer : Nat} {records : List (Record Name)} {built : Built Name}
    (hit : buildAt layerOf nameNode layer records = some built) (included : Subset built.observed reference)
    {ctx : Context} (level : ctx.layer = layer) (ordered : OrderedRecords records)
    (within : ∀ entry ∈ records, ctx.Contains entry.1) (leLayer : ∀ entry ∈ records, layerOf entry.1 ≤ layer)
    (rootLayer : ctx.root = true → layer = maxLayer layerOf records)
    (rootBounds : ctx.root = true → ctx.lower = none ∧ ctx.upper = none)
    (nonempty : ctx.root = false → records ≠ []) :
    Realizes layerOf reference (if ctx.root then none else some ctx) built.root records := by
  induction layer generalizing records built ctx with
  | zero | succ prior ih =>
    ·
      let descend : List (Record Name) → Option (Built Name) :=
        match ctx.layer with
        | 0 => fun _ => none
        | next + 1 => buildAt layerOf nameNode next
      have sound : ChildSound layerOf reference ctx.layer descend := by
        intro gap child next notEmpty ordered within below childLevel nonroot found includes
        first
        | solve | simp [descend, level] at found
        | simp only [descend, level] at found
          have low : ∀ entry ∈ gap, layerOf entry.1 ≤ prior := by
            intro entry mem
            have low := below entry mem
            omega
          have tree := ih found includes
            (by simpa [level] using childLevel) ordered within low (by simp [nonroot]) (by simp [nonroot]) (fun _ => notEmpty)
          simpa [nonroot] using tree
      rw [← level, buildAt.eq_def] at hit
      let split := splitLayer layerOf ctx.layer records
      change (do let filled ← assemble descend split.left split.pivots
                 let name ← nameNode filled.1
                 pure (⟨name, (name, filled.1) :: filled.2⟩ : Built Name)) = some built at hit
      cases filledEq : assemble descend split.left split.pivots <;> simp [filledEq] at hit
      rename_i filled
      cases named : nameNode filled.1 <;> simp [named] at hit
      rename_i name
      subst built
      have flat : split.flatten = records := split_flatten layerOf ctx.layer records
      have assembledFlat : LayerSplit.flatten ⟨split.left, split.pivots⟩ = records := flat
      obtain ⟨belowLeft, belowRight⟩ := split_gaps layerOf ctx.layer (level ▸ leLayer)
      obtain ⟨keys, missing, dry, groups, flatten, slots, interval, single, pruned, children⟩ :=
        assemble_spec sound (ctx := {ctx with layer := ctx.layer - 1, root := false}) rfl rfl
          (by rwa [assembledFlat]) (fun entry mem => within entry (assembledFlat ▸ mem)) belowLeft belowRight filledEq
          (fun pair mem => included (List.mem_cons_of_mem _ mem))
      obtain ⟨valid, rootCtx⟩ := assemble_valid ordered within (fun root => level.trans (rootLayer root)) nonempty
        (keys.trans (split_pivots layerOf ctx.layer records)) missing dry
      have present : reference name filled.1 := included (.head _)
      have same : (if ctx.root then none else some ctx).getD (filled.1.rootContext layerOf) = ctx := by
        cases root : ctx.root
        · simp
        · have height := rootCtx root
          obtain ⟨lower, upper⟩ := rootBounds root
          have eq : filled.1.rootContext layerOf = ctx := by
            cases ctx
            simp_all [Node.rootContext]
          simpa [root] using eq
      rw [← assembledFlat, ← flatten]
      exact .step present (by rwa [same]) (by rwa [same]) interval single pruned children

theorem build_realizes {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    {reference : Relation Name (Node Name)} {records : List (Record Name)} {built : Built Name}
    (hit : build layerOf nameNode records = some built) (included : Subset built.observed reference) :
    Realizes layerOf reference none built.root records := by
  unfold build at hit
  split at hit <;> rename_i ordered
  · let ctx : Context := ⟨maxLayer layerOf records, none, none, true⟩
    exact buildAt_realizes hit included (ctx := ctx) rfl ordered (by simp [ctx, Context.Contains])
      (maxLayer_spec layerOf records).1 (fun _ => rfl) (by simp [ctx]) (by simp [ctx])
  · simp at hit

private theorem assemble_blocks {descend : List (Record Name) → Option (Built Name)}
    {left : List (Record Name)} {pivots : List (Record Name × List (Record Name))}
    {result : Node Name × List (Name × Node Name)} (filled : assemble descend left pivots = some result)
    {pair : Name × Node Name} (mem : pair ∈ result.2) :
    ∃ input child, descend input = some child ∧ pair ∈ child.blocks := by
  have side_mem : ∀ gap side, buildGap descend gap = some side → pair ∈ side.2 →
      ∃ input child, descend input = some child ∧ pair ∈ child.blocks := by
    intro gap side found mem
    cases gap with
    | nil => cases (Option.some.inj found); simp at mem
    | cons head tail =>
      obtain ⟨child, hit, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨_, child, hit, mem⟩
  induction pivots generalizing left result with
  | nil =>
    obtain ⟨side, found, rfl⟩ := Option.map_eq_some_iff.mp filled
    exact side_mem left side found mem
  | cons head rest ih =>
    obtain ⟨pivot, right⟩ := head
    cases found : buildGap descend left <;> simp [assemble, found] at filled
    rename_i side
    cases suffix : assemble descend right rest <;> simp [suffix] at filled
    subst result
    exact (List.mem_append.mp mem).elim (side_mem _ _ found) (ih suffix)

private theorem step_names {nameNode : Node Name → Option Name} {split : LayerSplit Name}
    {descend : List (Record Name) → Option (Built Name)} {built : Built Name}
    (sound : ∀ ⦃input child⦄, descend input = some child → Subset child.observed (fun name node => nameNode node = some name))
    (hit : buildLayer nameNode descend split = some built) :
    Subset built.observed (fun name node => nameNode node = some name) := by
  cases assembly : assemble descend split.left split.pivots <;> simp [buildLayer, assembly] at hit
  rename_i filled
  cases named : nameNode filled.1 <;> simp [named] at hit
  subst built
  intro name node mem
  rcases List.mem_cons.mp mem with head | tail
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj head
    exact named
  · obtain ⟨_, _, builtChild, known⟩ := assemble_blocks assembly tail
    exact sound builtChild known

theorem build_names {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf nameNode records = some built) :
    Subset built.observed (fun name node => nameNode node = some name) := by
  have sound : ∀ layer {records : List (Record Name)} {built : Built Name},
      buildAt layerOf nameNode layer records = some built →
        Subset built.observed (fun name node => nameNode node = some name) := by
    intro layer
    induction layer with
    | zero =>
      intro records built hit
      rw [buildAt.eq_def] at hit
      exact step_names (split := splitLayer layerOf 0 records) (descend := fun _ => none) (by simp) hit
    | succ prior ih =>
      intro records built hit
      rw [buildAt.eq_def] at hit
      exact step_names (split := splitLayer layerOf (prior + 1) records) (fun {_ _} => ih) hit
  unfold build at hit
  split at hit
  · exact sound _ hit
  · simp at hit

private theorem assemble_total {layerOf : Key → Nat} {parent : Nat}
    {descend : List (Record Name) → Option (Built Name)}
    (total : ∀ gap, gap ≠ [] → Below layerOf parent gap → ∃ child, descend gap = some child)
    {left : List (Record Name)} {pivots : List (Record Name × List (Record Name))}
    (belowLeft : Below layerOf parent left) (belowRight : ∀ pivot ∈ pivots, Below layerOf parent pivot.2) :
    ∃ result, assemble descend left pivots = some result := by
  have gapTotal : ∀ gap, Below layerOf parent gap → ∃ result, buildGap descend gap = some result := by
    intro gap below
    cases gap with
    | nil => exact ⟨_, rfl⟩
    | cons head tail =>
      obtain ⟨child, named⟩ := total (head :: tail) (by simp) below
      exact ⟨(some child.root, child.blocks), by simp [buildGap, named]⟩
  induction pivots generalizing left with
  | nil =>
    obtain ⟨side, named⟩ := gapTotal left belowLeft
    exact ⟨(⟨side.1, []⟩, side.2), by simp [assemble, named]⟩
  | cons head rest ih =>
    obtain ⟨pivot, right⟩ := head
    obtain ⟨side, named⟩ := gapTotal left belowLeft
    obtain ⟨tail, next⟩ := ih (belowRight _ (.head _)) (fun pair mem => belowRight pair (.tail _ mem))
    exact ⟨(⟨side.1, ⟨pivot.1, pivot.2, tail.1.left⟩ :: tail.1.entries⟩, side.2 ++ tail.2), by simp [assemble, named, next]⟩

theorem build_total {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    (total : ∀ node, ∃ name, nameNode node = some name) {records : List (Record Name)}
    (ordered : OrderedRecords records) : ∃ built, build layerOf nameNode records = some built := by
  have go (layer : Nat) {records : List (Record Name)} (leLayer : ∀ record ∈ records, layerOf record.1 ≤ layer) :
      ∃ built, buildAt layerOf nameNode layer records = some built := by
    induction layer generalizing records with
    | zero | succ prior ih =>
      · let current := (by first | exact prior + 1 | exact 0 : Nat)
        let descend : List (Record Name) → Option (Built Name) :=
          match current with | 0 => fun _ => none | layer + 1 => buildAt layerOf nameNode layer
        have childTotal : ∀ gap, gap ≠ [] → Below layerOf current gap → ∃ child, descend gap = some child := by
          intro gap nonempty below
          first
          | solve
            | cases gap with
              | nil => exact (nonempty rfl).elim
              | cons head tail => exact (Nat.not_lt_zero _ (below head (.head _))).elim
          | exact ih (fun entry mem => Nat.le_of_lt_succ (below entry mem))
        obtain ⟨left, right⟩ := split_gaps layerOf current leLayer
        obtain ⟨result, filled⟩ := assemble_total (descend := descend) childTotal left right
        obtain ⟨name, named⟩ := total result.1
        refine ⟨⟨name, (name, result.1) :: result.2⟩, ?_⟩
        simp [buildAt.eq_def, buildLayer, current, descend, filled, named]
  simpa [build, ordered] using go (maxLayer layerOf records) (maxLayer_spec layerOf records).1

end Silmaril.Proofs.Formats.Dasl.MstBuild
