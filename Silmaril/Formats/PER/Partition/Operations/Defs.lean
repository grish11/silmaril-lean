module

public import Silmaril.Formats.PER.Partition.Thms

@[expose] public section

namespace Silmaril.Formats.PER.Partition

open Silmaril.Semantics

variable {Key : Type}

abbrev TotalMap (Key : Type) := Key → Key
abbrev PartialMap (Key : Type) := Key → Option Key
abbrev FiniteMap (Key : Type) [LinearOrder Key] := OrderedMap Key Key

def partialOfTotal (map : TotalMap Key) : PartialMap Key := some ∘ map

def totalOfPartial (map : PartialMap Key) (covered : ∀ key, (map key).isSome) : TotalMap Key :=
  fun key => (map key).get (covered key)

abbrev finiteLookup [LinearOrder Key] (map : FiniteMap Key) : PartialMap Key := map.lookup?

/-- Finite enumeration is supplied, not inferred. Keys outside the enumeration
are not queried and failures inside it stay absent. -/
abbrev tabulate [LinearOrder Key] (keys : Finset Key) (map : PartialMap Key) : FiniteMap Key :=
  OrderedMap.ofLookupOn keys map

/-- Algebraic idempotence for a total representative map. -/
def Idempotent (map : TotalMap Key) : Prop := ∀ key, map (map key) = map key

/-- Least common coarsening, not pointwise disjunction. This explicit binary
operation does not install a lattice instance or assume a residual. -/
def join (left right : PER Key) : PER Key :=
  PER.iInf fun upper : {upper : PER Key // left ≤ upper ∧ right ≤ upper} => upper.val

/-- One class on the two selected keys (one key if they coincide). -/
def identify (left right : Key) : PER Key :=
  (PER.universal Key).restrict fun key => key = left ∨ key = right

abbrev meet (left right : PER Key) : PER Key := left.intersection right

/-- Implication means entailment of the entire relation, not a pointwise PER
constructor or Heyting implication. -/
abbrev Entails (left right : PER Key) : Prop := left ≤ right

@[instance_reducible] def meetLabelsDecidable [LinearOrder Key] (left right : FiniteMap Key) :
    DecidableRel (meet (fibers left.lookup?) (fibers right.lookup?)).rel :=
  let l := fibers left.lookup?
  let r := fibers right.lookup?
  letI := labelsDecidable left.lookup?
  letI := labelsDecidable right.lookup?
  fun x y => inferInstanceAs (Decidable (l.rel x y ∧ r.rel x y))

def intersectMaps [LinearOrder Key] (left right : FiniteMap Key) : FiniteMap Key :=
  @canonicalOn _ _ left.keySet _ (meetLabelsDecidable left right)

/-- Filter the support while keeping the old labels; a retained key does not
need to retain its old representative as a key. -/
def restrictMap [LinearOrder Key] (labels : FiniteMap Key) (selected : Finset Key) : FiniteMap Key :=
  tabulate selected labels.lookup?

end Silmaril.Formats.PER.Partition
