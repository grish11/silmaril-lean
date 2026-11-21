module

public import Silmaril.Semantics.Prolly.Defs
public import Silmaril.Semantics.OrderedMap.Thms
import Silmaril.Proofs.Semantics.Prolly.Builder
import Silmaril.Proofs.Semantics.Prolly.Naming

public section

namespace Silmaril.Semantics.Prolly

variable {Key Payload Item Name : Type}

@[simp] theorem flatten_chunk (cut : Nat → Item → Bool) (items : List Item) : (chunk cut items).flatten = items :=
  Proofs.Semantics.Prolly.flatten_chunkFrom cut [] items

theorem chunk_canonical (cut : Nat → Item → Bool) (items : List Item) :
    chunk cut (chunk cut items).flatten = chunk cut items := by rw [flatten_chunk]

theorem lift_entries (level : Nat) (chunks : List (Node Key Payload level)) :
    flatten (level + 1) (lift chunks) = flatten level chunks.flatten :=
  Proofs.Semantics.Prolly.lift_entries level chunks

@[simp] theorem build_entries [LinearOrder Key] (policy : Policy Key) (map : OrderedMap Key Payload) :
    (build policy map).entries = map.entries :=
  Proofs.Semantics.Prolly.grow_entries policy map.entries.length 0 map.entries

theorem build_eq_of_lookup [LinearOrder Key] (policy : Policy Key) {left right : OrderedMap Key Payload}
    (same : ∀ key, left.lookup? key = right.lookup? key) : build policy left = build policy right :=
  congrArg (build policy) (OrderedMap.eq_of_lookup same)

/-- The common address function fixes the names of all children as well as the root. -/
theorem rootName_eq_of_lookup [LinearOrder Key] (policy : Policy Key) (address : Block Name Key Payload → Name)
    {left right : OrderedMap Key Payload} (same : ∀ key, left.lookup? key = right.lookup? key) :
    (build policy left).rootName address = (build policy right).rootName address :=
  congrArg (·.rootName address) (build_eq_of_lookup policy same)

theorem build_bounded [LinearOrder Key] (policy : Policy Key) (map : OrderedMap Key Payload) :
    (build policy map).Bounded policy.width :=
  Proofs.Semantics.Prolly.grow_bounded policy map.entries.length 0 map.entries (Nat.le_refl _) trivial

theorem Tree.rootName?_eq_some_iff (tree : Tree Key Payload)
    (nameBlock? : Block Name Key Payload → Option Name) (root : Name) :
    tree.rootName? nameBlock? = some root ↔
      ∃ address, tree.Admits nameBlock? address ∧ tree.rootName address = root :=
  Proofs.Semantics.Prolly.rootName_spec tree nameBlock? root

theorem Tree.replayAddress_spec (tree : Tree Key Payload) (nameBlock? : Block Name Key Payload → Option Name)
    {root : Name} (offDomain : Name) (hit : tree.rootName? nameBlock? = some root) :
    tree.Admits nameBlock? (replayAddress nameBlock? offDomain) ∧
      tree.rootName (replayAddress nameBlock? offDomain) = root :=
  Proofs.Semantics.Prolly.replayAddress_spec tree nameBlock? root offDomain hit

theorem Tree.observations_subset_iff (tree : Tree Key Payload) (address : Block Name Key Payload → Name)
    (reference : Naming.Relation Name (Block Name Key Payload)) :
    Naming.Subset (tree.observations address) reference ↔
    ∀ block ∈ blockOccurrences address tree.level tree.root, reference (address block) block :=
  ⟨fun incl _ hit => incl ⟨rfl, hit⟩, fun all _ _ ⟨same, hit⟩ => same.symm ▸ all _ hit⟩

end Silmaril.Semantics.Prolly
