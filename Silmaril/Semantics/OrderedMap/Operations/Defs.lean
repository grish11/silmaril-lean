module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Semantics.OrderedMap.Thms

@[expose] public section

namespace Silmaril.Semantics.OrderedMap

variable {Key Payload Error : Type} [LinearOrder Key]

def domain (map : OrderedMap Key Payload) : Finset Key := map.keys.toFinset

def cardinality (map : OrderedMap Key Payload) : Nat := map.entries.length

/-- Domain inclusion ignores payloads. Submap inclusion preserves every entry. -/
def domainSubset (left right : OrderedMap Key Payload) : Bool := decide (left.domain ⊆ right.domain)

def submap [DecidableEq Payload] (left right : OrderedMap Key Payload) : Bool :=
  left.entries.all fun entry => decide (right.lookup? entry.1 = some entry.2)

inductive Combine where
  | union
  | intersection
  deriving DecidableEq

/-- Invoked only for a shared key. `none` drops the key, not the computation. -/
abbrev Overlap (Key Payload Error : Type) := Key → Payload → Payload → Except Error (Option Payload)

namespace Overlap

def keepLeft : Overlap Key Payload Error := fun _ left _ => .ok (some left)

def keepRight : Overlap Key Payload Error := fun _ _ right => .ok (some right)

def reject : Overlap Key Payload Key := fun key _ _ => .error key

def discard : Overlap Key Payload Error := fun _ _ _ => .ok none

end Overlap

/-- Pointwise reference semantics, independent of the carrier and tree layout. -/
def Combine.atKey (kind : Combine) (overlap : Overlap Key Payload Error) (key : Key)
    (left right : Option Payload) : Except Error (Option Payload) :=
  match left, right with
  | some left, some right => overlap key left right
  | _, _ => match kind with
    | .union => .ok (left.orElse fun _ => right)
    | .intersection => .ok none

structure Evaluation (keys : List Key) where
  map : OrderedMap Key Payload
  keys_mem : ∀ entry ∈ map.entries, entry.1 ∈ keys

/-- Evaluate in ascending key order, stopping at the first error. The returned
carrier is intrinsically sorted; there is no additional failure mode. -/
def evaluate (step : Key → Except Error (Option Payload)) :
    (keys : List Key) → keys.Pairwise (· < ·) → Except Error (Evaluation (Payload := Payload) keys)
  | [], _ => .ok ⟨⟨[], .nil⟩, by simp⟩
  | key :: tail, ordered => do
    let value ← step key
    let rest ← evaluate step tail ordered.of_cons
    match value with
    | none => pure ⟨rest.map, fun entry hit => List.mem_cons_of_mem _ (rest.keys_mem entry hit)⟩
    | some payload =>
      pure ⟨⟨(key, payload) :: rest.map.entries, List.pairwise_cons.mpr
        ⟨fun entry hit => (List.pairwise_cons.mp ordered).1 entry.1 (rest.keys_mem entry hit), rest.map.ordered⟩⟩,
        fun entry hit => (List.mem_cons.mp hit).elim (fun equal => equal ▸ List.mem_cons_self)
          (fun hit => List.mem_cons_of_mem _ (rest.keys_mem entry hit))⟩

def combine (kind : Combine) (overlap : Overlap Key Payload Error) (left right : OrderedMap Key Payload) :
    Except Error (OrderedMap Key Payload) :=
  let keys := left.domain ∪ right.domain
  (evaluate (fun key => kind.atKey overlap key (left.lookup? key) (right.lookup? key))
    (keys.sort (· ≤ ·)) (((keys.pairwise_sort (· ≤ ·)).and (keys.sort_nodup (· ≤ ·))).imp
      fun ordered => lt_of_le_of_ne ordered.1 ordered.2)).map Evaluation.map

end Silmaril.Semantics.OrderedMap

namespace Silmaril.Semantics.OrderedSet

open OrderedMap (Combine Overlap)

variable {Key Error : Type} [LinearOrder Key]

def combine (kind : Combine) (overlap : Overlap Key Unit Error) (left right : OrderedSet Key) :
    Except Error (OrderedSet Key) := OrderedMap.combine kind overlap left right

end Silmaril.Semantics.OrderedSet
