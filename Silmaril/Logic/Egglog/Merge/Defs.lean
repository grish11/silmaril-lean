module

public import Mathlib.Order.Lattice
public import Mathlib.Logic.Function.Basic

@[expose] public section

namespace Silmaril.Logic.Egglog.Merge

/-- An operational dictionary can lack an entry. Lattice merge handles FD collisions;
it is separate from equality-table union and no-merge conflict checking. -/
abbrev Table (Key Value : Type) := Key → Option Value

variable {Key Value : Type} [DecidableEq Key] [SemilatticeSup Value]

/-- A set action inserts a new value or joins it with an existing value. -/
def write (table : Table Key Value) (key : Key) (new : Value) : Table Key Value :=
  Function.update table key (some (match table key with | none => new | some old => old ⊔ new))

/-- A stable semantic interpretation treats stored lattice information as a lower bound.
Exact lookup equality is a snapshot query and need not survive further writes. -/
def Sound (ideal : Key → Value) (table : Table Key Value) : Prop :=
  ∀ key value, table key = some value → value ≤ ideal key

end Silmaril.Logic.Egglog.Merge
