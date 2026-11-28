module

public import Silmaril.SSA.PEG.Reindex.Defs
public import Init.Data.Vector.OfFn

/-! # Rooted inference of a PEG renumbering

Corresponding roots and any supplied anchors seed a worklist. A fresh
row pair contributes every ordered operand pair and its loop label.
A fresh loop pair contributes its parent pair. Previously paired rows
and loops are checked for consistency and do not expand again. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Reindex.Automatic

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n n' l l' : Nat}

/-- Materialize rows and parents for repeated worklist reads. The
reference-table check still receives the original graphs. -/
def cacheRows (g : Graph P params results n l) : Graph P params results n l :=
  let rows := Vector.ofFn fun (i : Fin n) =>
    (⟨i, g.node i⟩ : Σ j, Node P params (Fin l) g.sort (g.sort j))
  let parents := Vector.ofFn g.forest.parent
  { g with
    forest := ⟨parents.get⟩
    node := fun i =>
      let row := rows.get i
      have address : row.1 = i := by simp [row, rows, Vector.get, Fin.cast]
      address ▸ row.2 }

def refIds {sort : Fin n → Ty Data} : {ts : List (Ty Data)} → Tuple (Ref sort) ts → List (Fin n)
  | _, .nil => []
  | _, .cons r tail => r.id :: refIds tail

abbrev Pairs (n n' : Nat) := List (Fin n × Fin n')

def Pairs.forward (pairs : Pairs n n') (a : Fin n) : Option (Fin n') :=
  (pairs.find? (fun pair => pair.1 == a)).map Prod.snd

def Pairs.backward (pairs : Pairs n n') (b : Fin n') : Option (Fin n) :=
  (pairs.find? (fun pair => pair.2 == b)).map Prod.fst

/-- A fresh pair must claim both endpoints. An already consistent pair
returns a false freshness flag. -/
def Pairs.insert (pairs : Pairs n n') (a : Fin n) (b : Fin n') : Option (Bool × Pairs n n') :=
  match pairs.forward a, pairs.backward b with
  | some next, some prior => if next = b ∧ prior = a then some (false, pairs) else none
  | none, none => some (true, (a, b) :: pairs)
  | _, _ => none

def Pairs.equiv (pairs : Pairs n n') : Option (Fin n' ≃ Fin n) :=
  if back : ∀ b, (pairs.backward b).isSome then
    if forth : ∀ a, (pairs.forward a).isSome then
      checkFinEquiv (fun b => (pairs.backward b).get (back b))
        (fun a => (pairs.forward a).get (forth a))
    else none
  else none

structure Matches (n n' l l' : Nat) where
  rows : Pairs n n'
  loops : Pairs l l'

abbrev Task (n n' l l' : Nat) := (Fin n × Fin n') ⊕ (Fin l × Fin l')

/-- Optional loop links may only be paired with links of the same shape. -/
def loopTasks (a : Option (Fin l)) (b : Option (Fin l')) : Option (List (Task n n' l l')) :=
  match a, b with
  | none, none => some []
  | some i, some j => some [.inr (i, j)]
  | _, _ => none

def visit [DecidableEq Data] (old : Graph P params results n l)
    (new : Graph P params results n' l') :
    Nat → List (Task n n' l l') → Matches n n' l l' → Option (Matches n n' l l')
  | _, [], pairs => some pairs
  | 0, _ :: _, _ => none
  | gas + 1, .inl (a, b) :: rest, pairs => do
    let (fresh, rows) ← pairs.rows.insert a b
    if fresh then
      let left := old.node a
      let right := new.node b
      if old.sort a = new.sort b ∧ left.inputs = right.inputs then
        let loops ← loopTasks left.label.loop right.label.loop
        let operands := (refIds left.args).zip (refIds right.args)
        visit old new gas (operands.map Sum.inl ++ loops ++ rest) { pairs with rows }
      else none
    else visit old new gas rest pairs
  | gas + 1, .inr (a, b) :: rest, pairs => do
    let (fresh, loops) ← pairs.loops.insert a b
    if fresh then
      let parents ← loopTasks (old.forest.parent a) (new.forest.parent b)
      visit old new gas (parents ++ rest) { pairs with loops }
    else visit old new gas rest pairs
termination_by structural gas _ _ => gas

/-- A remaining key has no label or paired descendant. Only parentless
unused keys may be paired by numerical order. -/
def finishLoops (old : LoopForest l) (new : LoopForest l') (pairs : Pairs l l') :
    Option (Fin l' ≃ Fin l) := do
  let oldFree := (List.finRange l).filter (fun i => (pairs.forward i).isNone)
  let newFree := (List.finRange l').filter (fun i => (pairs.backward i).isNone)
  if oldFree.length = newFree.length ∧
      oldFree.all (fun i => (old.parent i).isNone) ∧
      newFree.all (fun i => (new.parent i).isNone) then
    Pairs.equiv (pairs ++ oldFree.zip newFree)
  else none

structure Certificate (old : Graph P params results n l) (new : Graph P params results n' l') where
  rows : Fin n' ≃ Fin n
  loops : Fin l' ≃ Fin l
  checked : old.ReindexCertificate new rows loops

/-- Infer a candidate mapping from roots and additional row anchors.
Every row must be covered. Only unused loop keys have an order-based
fallback. The complete mapped table is compared before admission. -/
def infer [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (old : Graph P params results n l) (new : Graph P params results n' l')
    (anchors : Pairs n n' := []) : Option (Certificate old new) := do
  let seeds := (refIds old.roots).zip (refIds new.roots) ++ anchors
  let oldRows := cacheRows old
  let newRows := cacheRows new
  -- Each old row expands at most once, contributing its operands and at
  -- most one loop label. Each old loop contributes at most one parent.
  let operandCount := ((List.finRange n).map (fun i => (oldRows.node i).inputs.length)).sum
  let some pairs := visit oldRows newRows (seeds.length + operandCount + n + l)
    (seeds.map Sum.inl) ⟨[], []⟩ | none
  let some rows := pairs.rows.equiv | none
  let some loops := finishLoops oldRows.forest newRows.forest pairs.loops | none
  let accepted ← old.checkReindex new rows loops
  return ⟨rows, loops, accepted⟩

end Silmaril.SSA.PEG.Reindex.Automatic
