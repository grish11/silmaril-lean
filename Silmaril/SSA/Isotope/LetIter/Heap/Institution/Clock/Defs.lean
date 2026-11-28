module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Defs

/-! # The shared heap-plus-clock example model -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)

inductive Clock : Type → Type where
  | tick : Clock Bool

abbrev clockSignature : ITree.Signature := ⟨Clock⟩

def clockStep : Handler Nat Clock
  | ⟨_, .tick⟩, x, r, y => r = true ∧ y = x + 1

def heapClockModel (I : Type) : Model.{0,0} ((heapSignature I).sum clockSignature) where
  State := Store I × Nat
  initial x := x.2 = 0
  step
    | ⟨_, .inl ev⟩, x, r, y => step ⟨_, ev⟩ x.1 r y.1 ∧ y.2 = x.2
    | ⟨_, .inr ev⟩, x, r, y => clockStep ⟨_, ev⟩ x.2 r y.2 ∧ y.1 = x.1

end Silmaril.Isotope.LetIter.Heap
