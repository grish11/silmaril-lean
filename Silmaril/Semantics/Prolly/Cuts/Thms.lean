module

public import Silmaril.Semantics.Prolly.Cuts.Defs
public import Silmaril.Semantics.Prolly.Thms
import Silmaril.Proofs.Semantics.Prolly.Cuts

public section

namespace Silmaril.Semantics.Prolly

variable {Item Key Payload : Type}

/-- The executable chunker is exactly the unique partition obeying the cut rule. -/
theorem chunk_eq_iff (cut : Nat → Item → Bool) {items : List Item} {groups : List (List Item)} :
    chunk cut items = groups ↔ groups.flatten = items ∧ CutPartition cut groups :=
  ⟨fun same => same ▸ ⟨flatten_chunk cut items, Proofs.Semantics.Prolly.Cuts.partition_chunk cut items⟩,
   fun ⟨whole, valid⟩ => whole ▸ Proofs.Semantics.Prolly.Cuts.partition_rebuild valid⟩

theorem CanonicalGrowth.executes {policy : Policy Key} {level : Nat} {node : Node Key Payload level}
    {tree : Tree Key Payload} (canonical : CanonicalGrowth policy level node tree) {fuel : Nat}
    (enough : tree.level ≤ level + fuel) : grow policy fuel level node = tree :=
  Proofs.Semantics.Prolly.Cuts.growth_executes canonical enough

theorem build_canonical [LinearOrder Key] (policy : Policy Key) (map : Silmaril.Semantics.OrderedMap Key Payload) :
    CanonicalGrowth policy 0 map.entries (build policy map) :=
  Proofs.Semantics.Prolly.Cuts.build_canonical policy map

/-- No second output can satisfy the declarative builder, regardless of fuel. -/
theorem CanonicalGrowth.unique {policy : Policy Key} {level : Nat} {node : Node Key Payload level}
    {left right : Tree Key Payload} (first : CanonicalGrowth policy level node left)
    (second : CanonicalGrowth policy level node right) : left = right :=
  (first.executes (fuel := left.level + right.level) (by omega)).symm.trans (second.executes (by omega))

end Silmaril.Semantics.Prolly
