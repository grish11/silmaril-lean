module

public import Mathlib.Data.Set.Finite.Basic
public import Silmaril.Semantics.OrderedMap.Finite.Defs
public import Silmaril.Semantics.OrderedMap.Thms
import Silmaril.Proofs.Semantics.OrderedMap.Finite

public section

namespace Silmaril.Semantics.OrderedMap

variable {Key Item : Type} [LinearOrder Key]

@[simp] theorem lookup_ofLookupOn (keys : Finset Key) (lookup : Key → Option Item) (key : Key) :
    (ofLookupOn keys lookup).lookup? key = if key ∈ keys then lookup key else none :=
  Proofs.Semantics.OrderedMapFinite.lookup_ofLookupOn keys lookup key

@[simp] theorem mem_keySet (map : OrderedMap Key Item) (key : Key) :
    key ∈ map.keySet ↔ (map.lookup? key).isSome :=
  Proofs.Semantics.OrderedMapFinite.mem_keySet map key

theorem finite_support_iff (lookup : Key → Option Item) :
    (support lookup).Finite ↔ ∃ map : OrderedMap Key Item, map.lookup? = lookup :=
  Proofs.Semantics.OrderedMapFinite.finite_support_iff lookup

@[simp] theorem ofLookupOn_keySet (map : OrderedMap Key Item) :
    ofLookupOn map.keySet map.lookup? = map :=
  eq_of_lookup fun key => by cases hit : map.lookup? key <;> simp [hit]

@[simp] theorem lookup_transport {OtherKey OtherItem : Type} [LinearOrder OtherKey]
    (key : Key ≃ OtherKey) (item : Item ≃ OtherItem) (map : OrderedMap Key Item) (other : OtherKey) :
    (transport key item map).lookup? other = (map.lookup? (key.symm other)).map item :=
  Proofs.Semantics.OrderedMapFinite.lookup_transport key item map other

/-- A change of key equality and value representation preserves extensional maps.
The key equivalence need not preserve order. -/
def transportEquiv {OtherKey OtherItem : Type} [LinearOrder OtherKey]
    (key : Key ≃ OtherKey) (item : Item ≃ OtherItem) :
    OrderedMap Key Item ≃ OrderedMap OtherKey OtherItem where
  toFun := transport key item
  invFun := transport key.symm item.symm
  left_inv map := eq_of_lookup fun src => by cases hit : map.lookup? src <;> simp [hit]
  right_inv map := eq_of_lookup fun dst => by cases hit : map.lookup? dst <;> simp [hit]

end Silmaril.Semantics.OrderedMap

namespace Silmaril.Semantics.OrderedSet

variable {Key : Type} [LinearOrder Key]

@[simp] theorem ofFinset_lookup (keys : Finset Key) (key : Key) :
    (ofFinset keys).lookup? key = if key ∈ keys then some () else none :=
  Proofs.Semantics.OrderedMapFinite.set_lookup keys key

def finsetEquiv : Finset Key ≃ OrderedSet Key where
  toFun := ofFinset
  invFun := OrderedMap.keySet
  left_inv keys := Finset.ext fun key => by by_cases mem : key ∈ keys <;> simp [mem]
  right_inv set := OrderedMap.eq_of_lookup fun key => by cases hit : set.lookup? key <;> simp [hit]

end Silmaril.Semantics.OrderedSet
