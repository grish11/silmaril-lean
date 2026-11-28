module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Setoid.Basic
public import Silmaril.Formats.SExp.Basic

/-!
# Arenas of dotted S-expressions

Each encoding is read through a partial cell lookup. A stored `Cell.nil` denotes the
empty S-expression. A hole (including an out-of-bounds list index) has no finite
unfolding. A pair must unfold both children, so dangling children and reachable cycles
also prevent an unfolding.
-/

@[expose] public section

namespace Silmaril.Formats.SExpArena

universe ui uj ua ue ur
variable {Ix : Type ui} {Jx : Type uj} {Atom : Type ua} {Entry : Type ue} {R : Type ur}

/-- A pair of references, in car/cdr order. The two references may be equal. -/
structure Cons (Ix : Type ui) where
  car : Ix
  cdr : Ix
  deriving DecidableEq, Repr

inductive Cell (Ix : Type ui) (Atom : Type ua) where
  | nil
  | atom (value : Atom)
  | cons (pair : Cons Ix)
  deriving DecidableEq, Repr

def Cell.mapIndices (rename : Ix → Jx) : Cell Ix Atom → Cell Jx Atom
  | .nil => .nil
  | .atom value => .atom value
  | .cons pair => .cons ⟨rename pair.car, rename pair.cdr⟩

/-- An explicit undefined sentinel for encodings with a hole at a stored position. -/
inductive Undef (Entry : Type ue) where
  | undef
  | defined (entry : Entry)
  deriving DecidableEq, Repr

/-- How to read one stored entry. The index and atom types are inferred from the encoding. -/
class CellEncoding (Entry : Type ue) (Ix : outParam (Type ui)) (Atom : outParam (Type ua)) where
  decode : Entry → Option (Cell Ix Atom)

instance : CellEncoding (Cell Ix Atom) Ix Atom where
  decode := some

/-- The right lane contains atoms. Use a `Cell` encoding to store a distinguished nil. -/
instance : CellEncoding (Cons Ix ⊕ Atom) Ix Atom where
  decode
    | .inl pair => some (.cons pair)
    | .inr value => some (.atom value)

instance [CellEncoding Entry Ix Atom] : CellEncoding (Option Entry) Ix Atom where
  decode entry := entry.bind CellEncoding.decode

instance [CellEncoding Entry Ix Atom] : CellEncoding (Undef Entry) Ix Atom where
  decode
    | .undef => none
    | .defined entry => CellEncoding.decode entry

/-- The shared semantic interface for all storage representations. -/
abbrev Arena (Ix : Type ui) (Atom : Type ua) := Ix → Option (Cell Ix Atom)

namespace Arena

def ofMap [CellEncoding Entry Ix Atom] (entries : Ix → Entry) : Arena Ix Atom :=
  fun index => CellEncoding.decode (entries index)

def ofList [CellEncoding Entry Nat Atom] (entries : List Entry) : Arena Nat Atom :=
  fun index => entries[index]?.bind CellEncoding.decode

/-- An absent whole arena has no readable cells. -/
def ofOption (storage : Option (Arena Ix Atom)) : Arena Ix Atom :=
  fun index => storage.bind (· index)

def ofUndef : Undef (Arena Ix Atom) → Arena Ix Atom
  | .undef => fun _ => none
  | .defined arena => arena

/-- Finite unfolding duplicates shared subgraphs in the resulting expression. -/
inductive Unfolds (arena : Arena Ix Atom) : Ix → SExp2 Atom → Prop where
  | nil {index} : arena index = some .nil → Unfolds arena index .nil
  | atom {index value} : arena index = some (.atom value) → Unfolds arena index (.atom value)
  | cons {index pair car cdr} : arena index = some (.cons pair) →
      Unfolds arena pair.car car → Unfolds arena pair.cdr cdr → Unfolds arena index (.cons car cdr)

/-- Every finite expression present at any index. -/
def denotation (arena : Arena Ix Atom) : Set (SExp2 Atom) :=
  {expr | ∃ index, arena.Unfolds index expr}

def exportDenotation (arena : Arena Ix Atom) (exports : List Ix) : Set (SExp2 Atom) :=
  {expr | ∃ index ∈ exports, arena.Unfolds index expr}

/-- From a cons to either child, including a child whose lookup is missing. -/
def Edge (arena : Arena Ix Atom) (parent child : Ix) : Prop :=
  ∃ pair, arena parent = some (.cons pair) ∧ (child = pair.car ∨ child = pair.cdr)

abbrev Reachable (arena : Arena Ix Atom) := Relation.ReflTransGen arena.Edge
abbrev ChildPath (arena : Arena Ix Atom) := Relation.TransGen arena.Edge

def ReachableFrom (arena : Arena Ix Atom) (exports : List Ix) (index : Ix) : Prop :=
  ∃ root ∈ exports, arena.Reachable root index

def Cyclic (arena : Arena Ix Atom) : Prop :=
  ∃ index, arena.ChildPath index index

def Acyclic (arena : Arena Ix Atom) : Prop := ¬ arena.Cyclic

def CyclicBelow (arena : Arena Ix Atom) (root : Ix) : Prop :=
  ∃ index, arena.Reachable root index ∧ arena.ChildPath index index

def AcyclicBelow (arena : Arena Ix Atom) (root : Ix) : Prop := ¬ arena.CyclicBelow root

/-- The target agrees on all indices reachable in the source, including exports
and reachable indices with a failed lookup. -/
def PreservesReachable (source target : Arena Ix Atom) (exports : List Ix) : Prop :=
  ∀ index, source.ReachableFrom exports index → target index = source index

/-- Reindex all cells reachable from the exports, mapping both ordered children.
The target may contain additional cells elsewhere. -/
def Reindexes (source : Arena Ix Atom) (target : Arena Jx Atom) (exports : List Ix)
    (rename : Ix → Jx) : Prop :=
  ∀ index, source.ReachableFrom exports index →
    target (rename index) = (source index).map (Cell.mapIndices rename)

/-- Delete all entries outside a supplied set of indices. -/
def restrict (arena : Arena Ix Atom) (keep : Ix → Prop) [DecidablePred keep] : Arena Ix Atom :=
  fun index => if keep index then arena index else none

/-- Mark by reachability and sweep the remaining indices. This is a specification
using classical reachability, with `restrict` available for decidable masks. -/
noncomputable def markSweep (arena : Arena Ix Atom) (exports : List Ix) : Arena Ix Atom :=
  @restrict _ _ arena (arena.ReachableFrom exports) (Classical.decPred _)

end Arena

/-- One root in an arena. Failed unfoldings all have the empty denotation. -/
structure Pointed (Ix : Type ui) (Atom : Type ua) where
  index : Ix
  arena : Arena Ix Atom

def Pointed.denotation (point : Pointed Ix Atom) : Set (SExp2 Atom) :=
  {expr | point.arena.Unfolds point.index expr}

instance : Setoid (Pointed Ix Atom) := Setoid.ker Pointed.denotation

/-- A type of root descriptors with an inferred index type. -/
class Root (R : Type ur) (Ix : outParam (Type ui)) where
  indices : R → List Ix

instance : Root (List Ix) Ix := ⟨id⟩

instance [Root R Ix] : CoeOut R (List Ix) := ⟨Root.indices⟩

structure Rooted (Ix : Type ui) (Atom : Type ua) (R : Type ur) where
  roots : R
  arena : Arena Ix Atom

abbrev Exported (Ix : Type ui) (Atom : Type ua) := Rooted Ix Atom (List Ix)

def Rooted.denotation [Root R Ix] (rooted : Rooted Ix Atom R) : Set (SExp2 Atom) :=
  rooted.arena.exportDenotation (Root.indices rooted.roots)

instance [Root R Ix] : Setoid (Rooted Ix Atom R) := Setoid.ker Rooted.denotation

def Pointed.toExports (point : Pointed Ix Atom) : Exported Ix Atom :=
  ⟨[point.index], point.arena⟩

noncomputable def Rooted.markSweep [Root R Ix] (rooted : Rooted Ix Atom R) : Rooted Ix Atom R :=
  ⟨rooted.roots, rooted.arena.markSweep (Root.indices rooted.roots)⟩

/-- A partial map with a finite cover of its domain. The cover may include holes. -/
structure FiniteLookup (Ix : Type ui) (Entry : Type ue) where
  keys : Finset Ix
  lookup : Ix → Option Entry
  none_of_not_mem : ∀ index ∉ keys, lookup index = none

namespace FiniteLookup

def ofList (entries : List Entry) : FiniteLookup Nat Entry where
  keys := Finset.range entries.length
  lookup index := entries[index]?
  none_of_not_mem _ outside :=
    List.getElem?_eq_none (Nat.le_of_not_lt fun inside => outside (Finset.mem_range.mpr inside))

def mapEntries {New : Type*} (storage : FiniteLookup Ix Entry) (f : Ix → Entry → Option New) :
    FiniteLookup Ix New where
  keys := storage.keys
  lookup index := (storage.lookup index).bind (f index)
  none_of_not_mem index outside := by rw [storage.none_of_not_mem index outside]; rfl

def normalize [CellEncoding Entry Ix Atom] (storage : FiniteLookup Ix Entry) :
    FiniteLookup Ix (Cell Ix Atom) :=
  storage.mapEntries fun _ => CellEncoding.decode

def restrict (storage : FiniteLookup Ix Entry) (keep : Ix → Prop) [DecidablePred keep] :
    FiniteLookup Ix Entry where
  keys := storage.keys.filter keep
  lookup index := if keep index then storage.lookup index else none
  none_of_not_mem index outside := by
    by_cases kept : keep index
    · simp [kept, storage.none_of_not_mem index fun inside =>
        outside (Finset.mem_filter.mpr ⟨inside, kept⟩)]
    · simp [kept]

/-- Sweep finite storage using the reachability of its decoded cells. -/
noncomputable def markSweep [CellEncoding Entry Ix Atom] (storage : FiniteLookup Ix Entry)
    (exports : List Ix) : FiniteLookup Ix Entry := by
  classical
  exact storage.restrict (Arena.ReachableFrom storage.normalize.lookup exports)

/-- The number of incoming internal references to the index. A cons that points
to the same index twice contributes two. External exports are counted separately
by their list occurrences, and do not contribute here. -/
def incomingCount [DecidableEq Ix] (storage : FiniteLookup Ix (Cell Ix Atom)) (target : Ix) : Nat :=
  Finset.sum storage.keys fun source =>
    match storage.lookup source with
    | some (.cons pair) => (if pair.car = target then 1 else 0) + (if pair.cdr = target then 1 else 0)
    | _ => 0

end FiniteLookup

/-- Each occupied entry stores a cell and its internal reference count. -/
abbrev RefCounted (Ix : Type ui) (Atom : Type ua) := FiniteLookup Ix (Cell Ix Atom × Nat)

namespace RefCounted

def erase (storage : RefCounted Ix Atom) : FiniteLookup Ix (Cell Ix Atom) :=
  storage.mapEntries fun _ entry => some entry.1

def count? (storage : RefCounted Ix Atom) (index : Ix) : Option Nat :=
  (storage.lookup index).map Prod.snd

/-- A count is required for each stored cell. Dangling targets have no stored count. -/
def CountsCorrect [DecidableEq Ix] (storage : RefCounted Ix Atom) : Prop :=
  ∀ index count, storage.count? index = some count → count = storage.erase.incomingCount index

end RefCounted

/-- Populate counts from all occupied internal sources. -/
def FiniteLookup.withRefCounts [DecidableEq Ix] (storage : FiniteLookup Ix (Cell Ix Atom)) :
    RefCounted Ix Atom :=
  storage.mapEntries fun index cell => some (cell, storage.incomingCount index)

end Silmaril.Formats.SExpArena
