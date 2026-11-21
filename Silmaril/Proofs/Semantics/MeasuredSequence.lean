module

public import Silmaril.Semantics.MeasuredSequence.Defs

public section

namespace Silmaril.Proofs.Semantics.MeasuredSequence

open Silmaril.Semantics.MeasuredSequence

variable {Item : Type} {tree left right : Tree Item}

theorem sizeSpec (valid : Valid tree) : size tree = (flatten tree).length := by
  induction tree with
  | empty => rfl
  | one item => rfl
  | branch length left right ihLeft ihRight =>
    obtain ⟨validLeft, validRight, _, _, total⟩ := valid
    simp only [size, flatten, List.length_append]
    rw [← ihLeft validLeft, ← ihRight validRight, ← total]

theorem appendValid (validLeft : Valid left) (validRight : Valid right) : Valid (append left right) := by
  cases left <;> cases right <;> simp_all [append, Valid, size] <;> omega

theorem flattenAppend (left right : Tree Item) : flatten (append left right) = flatten left ++ flatten right := by
  cases left <;> cases right <;> simp [append, flatten]

theorem getSpec (valid : Valid tree) (index : Nat) : get? tree index = (flatten tree)[index]? := by
  induction tree generalizing index with
  | empty => rfl
  | one item => cases index <;> rfl
  | branch length left right ihLeft ihRight =>
    obtain ⟨validLeft, validRight, _, _, _⟩ := valid
    simp only [get?, flatten, List.getElem?_append, ← sizeSpec validLeft, ihLeft validLeft, ihRight validRight]

private theorem sizeSet (tree : Tree Item) (index : Nat) (item : Item) : size (set tree index item) = size tree := by
  cases tree with
  | empty => rfl
  | one old => cases index <;> rfl
  | branch length left right => rw [Silmaril.Semantics.MeasuredSequence.set]; split <;> rfl

theorem setValid (valid : Valid tree) (index : Nat) (item : Item) : Valid (set tree index item) := by
  induction tree generalizing index with
  | empty => trivial
  | one old => cases index <;> trivial
  | branch length left right ihLeft ihRight =>
    obtain ⟨validLeft, validRight, posLeft, posRight, total⟩ := valid
    simp only [Silmaril.Semantics.MeasuredSequence.set]
    split
    · simp only [Valid, sizeSet]
      exact ⟨ihLeft validLeft index, validRight, posLeft, posRight, total⟩
    · simp only [Valid, sizeSet]
      exact ⟨validLeft, ihRight validRight (index - size left), posLeft, posRight, total⟩

theorem setSpec (valid : Valid tree) (index : Nat) (item : Item) :
    flatten (set tree index item) = (flatten tree).set index item := by
  induction tree generalizing index with
  | empty => rfl
  | one old => cases index <;> rfl
  | branch length left right ihLeft ihRight =>
    obtain ⟨validLeft, validRight, _, _, _⟩ := valid
    simp only [Silmaril.Semantics.MeasuredSequence.set, flatten, List.set_append, ← sizeSpec validLeft]
    split
    · simp only [flatten, ihLeft validLeft]
    · simp only [flatten, ihRight validRight]

theorem splitValid (valid : Valid tree) (index : Nat) :
    Valid (splitAt tree index).1 ∧ Valid (splitAt tree index).2 := by
  induction tree generalizing index with
  | empty => exact ⟨trivial, trivial⟩
  | one item => cases index <;> exact ⟨trivial, trivial⟩
  | branch length left right ihLeft ihRight =>
    obtain ⟨validLeft, validRight, _, _, _⟩ := valid
    simp only [splitAt]
    split
    · exact ⟨(ihLeft validLeft _).1, appendValid (ihLeft validLeft _).2 validRight⟩
    · split
      · exact ⟨validLeft, validRight⟩
      · exact ⟨appendValid validLeft (ihRight validRight _).1, (ihRight validRight _).2⟩

theorem splitSpec (valid : Valid tree) (index : Nat) :
    flatten (splitAt tree index).1 = (flatten tree).take index ∧
      flatten (splitAt tree index).2 = (flatten tree).drop index := by
  induction tree generalizing index with
  | empty => simp [splitAt, flatten]
  | one item => cases index <;> simp [splitAt, flatten]
  | branch length left right ihLeft ihRight =>
    obtain ⟨validLeft, validRight, _, _, _⟩ := valid
    have sizeLeft := sizeSpec validLeft
    by_cases before : index < size left
    · have lengthBound : index ≤ (flatten left).length := by omega
      simpa [splitAt, before, flatten, flattenAppend, List.take_append_of_le_length lengthBound,
        List.drop_append_of_le_length lengthBound] using ihLeft validLeft index
    · by_cases edge : index = size left
      · simp [splitAt, edge, sizeLeft, flatten]
      · have lengthBound : (flatten left).length ≤ index := by omega
        obtain ⟨takeRight, dropRight⟩ := ihRight validRight (index - size left)
        simp [splitAt, before, edge, flatten, flattenAppend, List.take_append, List.drop_append,
          List.take_of_length_le lengthBound, List.drop_eq_nil_of_le lengthBound, ← sizeLeft, takeRight, dropRight]

theorem spliceValid (valid : Valid tree) (validInsert : Valid right) (index count : Nat) :
    Valid (splice tree index count right) :=
  appendValid (splitValid valid index).1 (appendValid validInsert (splitValid (splitValid valid index).2 count).2)

theorem spliceSpec (valid : Valid tree) (index count : Nat) (inserted : Tree Item) :
    flatten (splice tree index count inserted) =
      (flatten tree).take index ++ (flatten inserted ++ ((flatten tree).drop index).drop count) := by
  have split := splitSpec valid index
  have rest := splitSpec (splitValid valid index).2 count
  simp only [splice, flattenAppend, split.1, rest.2, split.2]

private theorem buildValid (fuel : Nat) (items : List Item) : Valid (build fuel items) := by
  induction fuel generalizing items with
  | zero => trivial
  | succ fuel ih =>
    cases items with
    | nil => trivial
    | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest => exact appendValid (ih _) (ih _)

private theorem buildSpec (fuel : Nat) (items : List Item) (enough : items.length ≤ fuel) :
    flatten (build fuel items) = items := by
  induction fuel generalizing items with
  | zero =>
    cases items with
    | nil => rfl
    | cons first rest => simp at enough
  | succ fuel ih =>
    cases items with
    | nil => rfl
    | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
        let items := first :: second :: rest
        let midpoint := items.length / 2
        have lengthEq : items.length = rest.length + 2 := rfl
        have bound : items.length ≤ fuel + 1 := enough
        change flatten (append (build fuel (items.take midpoint)) (build fuel (items.drop midpoint))) = items
        rw [flattenAppend, ih _ (by simp only [List.length_take, midpoint]; omega),
          ih _ (by simp only [List.length_drop, midpoint]; omega), List.take_append_drop]

theorem ofListValid (items : List Item) : Valid (ofList items) := buildValid _ _

theorem ofListSpec (items : List Item) : flatten (ofList items) = items := buildSpec _ _ (Nat.le_refl _)

private theorem appendBranch {left right : Tree Item} (posLeft : 0 < size left) (posRight : 0 < size right) :
    append left right = .branch (size left + size right) left right := by
  cases left <;> cases right <;> first | rfl | contradiction

private theorem buildBisected (fuel : Nat) (items : List Item) (enough : items.length ≤ fuel) :
    Bisected (build fuel items) := by
  induction fuel generalizing items with
  | zero => trivial
  | succ fuel ih =>
    cases items with
    | nil => trivial
    | cons first rest =>
      cases rest with
      | nil => trivial
      | cons second rest =>
        let items := first :: second :: rest
        let midpoint := items.length / 2
        have lengthEq : items.length = rest.length + 2 := rfl
        have bound : items.length ≤ fuel + 1 := enough
        have takeSize : (items.take midpoint).length = midpoint := by
          rw [List.length_take, Nat.min_eq_left (by dsimp [midpoint]; omega)]
        have dropSize : (items.drop midpoint).length = items.length - midpoint := List.length_drop
        have takeFuel : (items.take midpoint).length ≤ fuel := by rw [takeSize]; dsimp [midpoint]; omega
        have dropFuel : (items.drop midpoint).length ≤ fuel := by rw [dropSize]; dsimp [midpoint]; omega
        let left := build fuel (items.take midpoint)
        let right := build fuel (items.drop midpoint)
        have leftSize : size left = midpoint := by
          rw [sizeSpec (buildValid _ _), buildSpec _ _ takeFuel, takeSize]
        have rightSize : size right = items.length - midpoint := by
          rw [sizeSpec (buildValid _ _), buildSpec _ _ dropFuel, dropSize]
        have posLeft : 0 < size left := by rw [leftSize]; dsimp [midpoint]; omega
        have posRight : 0 < size right := by rw [rightSize]; dsimp [midpoint]; omega
        change Bisected (append left right)
        rw [appendBranch posLeft posRight]
        refine ⟨?_, ih _ takeFuel, ih _ dropFuel⟩
        rw [leftSize, rightSize]
        dsimp [midpoint]
        omega

theorem ofListBisected (items : List Item) : Bisected (ofList items) :=
  buildBisected _ _ (Nat.le_refl _)

end Silmaril.Proofs.Semantics.MeasuredSequence
