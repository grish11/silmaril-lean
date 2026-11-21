module

public import Silmaril.Semantics.Prolly.Defs

@[expose] public section

namespace Silmaril.Semantics.Prolly

variable {Key : Type}

/-- Keys in the next builder frontier: take the last key in each chunk. -/
def keyStep (policy : Policy Key) (level : Nat) (keys : List Key) : List Key :=
  (chunk (policy.cut level) keys).filterMap List.getLast?

/-- Non-initial frontiers produced by `grow`, in order from leaves to root.
An input that already fits produces no new frontier. -/
def promotions (policy : Policy Key) : Nat → Nat → List Key → List (List Key)
  | 0, _, _ => []
  | fuel + 1, level, keys =>
    if keys.length ≤ policy.width then []
    else
      let parents := keyStep policy level keys
      parents :: promotions policy fuel (level + 1) parents

/-- A frontier that fits is terminal and has no input to the next cut. -/
def activeKeys (policy : Policy Key) (keys : List Key) : List Key :=
  if keys.length ≤ policy.width then [] else keys

/-- The frontier reached after `steps` transitions. After the root, the
trajectory is padded with empty lists. Start with `level := 0` for `build`. -/
def frontierAt (policy : Policy Key) : (steps level : Nat) → List Key → List Key
  | 0, _, keys => keys
  | steps + 1, level, keys => frontierAt policy steps (level + 1) (keyStep policy level (activeKeys policy keys))

end Silmaril.Semantics.Prolly
