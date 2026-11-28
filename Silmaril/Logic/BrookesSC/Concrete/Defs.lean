module

public import Silmaril.Logic.BrookesSC.Defs
public import Silmaril.Semantics.Brookes.Defs
public import Mathlib.Logic.Function.Basic

/-! # The SC signature target on finite Brookes behaviors -/

@[expose] public section

namespace Silmaril.Logic.BrookesSC.Concrete

open Silmaril.Semantics.Brookes

universe u

/-- A shared store for one world, with a possibly different value type at each cell
and one optional owner at each mutex. -/
structure Store (W : World.{u}) where
  memory : (cell : W.Cell) → W.Value cell
  owner : W.Mutex → Option W.Thread

variable {W : World.{u}} {A B : Type u}

section Primitive

variable [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread]

/-- One successful SC store step. Both access modes read or update memory in
the same way. Acquire needs a free mutex, and release needs the current owner. -/
def Store.step (p : Primitive W) (s : Store W) : Option (p.Reply × Store W) :=
  match p with
  | .load _ _ cell => some (s.memory cell, s)
  | .store _ _ cell value => some (⟨⟩, {s with memory := Function.update s.memory cell value})
  | .acquire thread mutex =>
      if s.owner mutex = none then
        some (⟨⟩, {s with owner := Function.update s.owner mutex (some thread)})
      else none
  | .release thread mutex =>
      if s.owner mutex = some thread then
        some (⟨⟩, {s with owner := Function.update s.owner mutex none})
      else none

/-- Close the singleton generators of the successful primitive steps. -/
def primitive (p : Primitive W) : Behavior (Store W) p.Reply :=
  Behavior.atomic fun s t reply => Store.step p s = some (reply, t)

end Primitive

/-- Inclusion of complete transition words with their replies. -/
def Includes (first second : Behavior (Store W) A) : Prop :=
  ∀ ⦃trace value⦄, first.accepts trace value → second.accepts trace value

end Silmaril.Logic.BrookesSC.Concrete
