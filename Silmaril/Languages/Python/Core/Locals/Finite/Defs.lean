module

public import Silmaril.Languages.Python.Core.Locals.Defs
public import Silmaril.Semantics.Operational.Environment.Finite.Defs
public import Silmaril.Semantics.Operational.Projection.Defs

/-! # Finite presentations of Python local-slot states

The existing Python `Store` is the semantic view. Association lists supply
finite witnesses with distinct keys. The `Fin slots` key type fixes the
layout, and the control and action types come from the typed locals model.
-/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Locals.Finite

open Semantics.Operational

variable {slots : Nat}

abbrev Rows (slots : Nat) := AList (fun _ : Fin slots => Int)

inductive Presentation (slots : Nat) where
  | evaluating (rows : Rows slots) (rhs : Rhs slots) (cont : Continuation slots)
  | raising (rows : Rows slots) (error : Error slots)
  | finished (rows : Rows slots) (result : Result slots)

def rowsOf (store : Store slots) : Rows slots :=
  Environment.Finite.encode store (List.finRange slots)

namespace Presentation

def encode : State slots → Presentation slots
  | .evaluating store rhs cont => .evaluating (rowsOf store) rhs cont
  | .raising store error => .raising (rowsOf store) error
  | .finished store result => .finished (rowsOf store) result

def view : Presentation slots → State slots
  | .evaluating rows rhs cont => .evaluating (Environment.Finite.view rows) rhs cont
  | .raising rows error => .raising (Environment.Finite.view rows) error
  | .finished rows result => .finished (Environment.Finite.view rows) result

def enter (rows : Rows slots) : Code slots → Presentation slots
  | .ret rhs => .evaluating rows rhs .ret
  | .assign slot rhs rest => .evaluating rows rhs (.assign slot rest)
  | .branch test yes no => .evaluating rows test (.branch yes no)

def resume (rows : Rows slots) (cont : Continuation slots) :
    Except (Error slots) (Rhs slots) → Presentation slots
  | .ok rhs => .evaluating rows rhs cont
  | .error error => .raising rows error

/-- Use the Core expression selector over finite lookup. An assignment
updates the chosen association list and emits the existing write event. -/
def advance : Presentation slots → Option (Option (Event slots) × Presentation slots)
  | .evaluating rows (.arithmetic (.int value)) cont =>
    match cont with
    | .ret => some (some (.exit (.ok value)), .finished rows (.ok value))
    | .assign slot rest => some (some (.write slot value), enter (rows.insert slot value) rest)
    | .branch yes no => some (none, enter rows (if value = 0 then no else yes))
  | .evaluating rows rhs cont =>
    (rhs.reduce (Environment.Finite.view rows)).map fun next => (none, resume rows cont next)
  | .raising rows error => some (some (.exit (.error error)), .finished rows (.error error))
  | .finished _ _ => none

/-- Only a finished frame has a terminal completion. Both success and a
defined exception use the existing result payload. -/
def completion? : Presentation slots → Option (Result slots)
  | .finished _ result => some result
  | .evaluating .. | .raising .. => none

end Presentation

def presented (slots : Nat) : Cslib.LTS (Presentation slots) (Option (Event slots)) :=
  ⟨fun source action target => source.advance = some (action, target)⟩

def semantic (slots : Nat) : Cslib.LTS (State slots) (Option (Event slots)) :=
  ⟨Step⟩

end Silmaril.Languages.Python.Core.Locals.Finite
