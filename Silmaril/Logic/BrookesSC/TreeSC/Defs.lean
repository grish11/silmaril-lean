module

public import Silmaril.Logic.BrookesSC.Concrete.Defs
public import Silmaril.Semantics.Brookes.StoreEquiv.Defs
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Defs

/-! The typed SC encoding of TreeSC's homogeneous read/write programs. -/

@[expose] public section

namespace Silmaril.Logic.BrookesSC.TreeSC

open CategoryTheory
open Silmaril.Semantics.Brookes.TreeSC (Code)
open Silmaril.Semantics.TrackA.Concurrency renaming AccessMode → TrackMode

/-- One thread, Nat-valued cells, and empty types of mutexes and external sorts. -/
abbrev world (R : Type) : World where
  Thread := Unit
  Cell := R
  Value := fun _ => Nat
  Mutex := Empty
  ExternalSort := Empty
  ExternalReply := Empty.elim

/-- A concrete store has exactly the TreeSC memory and a unique empty owner map. -/
def storeEquiv (R : Type) :
    Silmaril.Semantics.Brookes.TreeSC.Store R ≃ Concrete.Store (world R) where
  toFun s := ⟨s, Empty.elim⟩
  invFun s := s.memory
  left_inv _ := rfl
  right_inv := by
    rintro ⟨memory, owner⟩
    have h : (Empty.elim : Empty → Option Unit) = owner := funext fun lock => nomatch lock
    cases h
    rfl

/-- Keep the tag in the designation even though both modes have the same SC effect. -/
def accessMode : TrackMode → BrookesSC.AccessMode
  | .plain => .plain
  | .scAtomic => .scAtomic

/-- A label for each designation. The world has no external or mutex designation. -/
def signature (R : Type) : Signature (world R) where
  Op _ := Unit

variable {R X : Type} {S : Signature (world R)}

/-- Encode using the selected label in each designation fiber. The load's Nat
reply chooses its continuation. A write's unique PUnit reply stands for Unit. -/
def encode (labels : signature R ⟶ S) : Code R → Program S Unit
  | .done => .ret ()
  | .load mode loc next =>
      .call (d := .primitive (.load () (accessMode mode) loc)) (labels.label ())
        (fun reply => encode labels (next reply))
  | .store mode loc value next =>
      .call (d := .primitive (.store () (accessMode mode) loc value)) (labels.label ())
        (fun _ => encode labels next)
  | .acquire lock _ | .release lock _ => nomatch lock

/-- A pointwise inclusion judgment with the given type of input valuations. -/
def inequation (labels : signature R ⟶ S) (lhs rhs : X → Code R) : Sentence S where
  Input := X
  Result := Unit
  lhs x := encode labels (lhs x)
  rhs x := encode labels (rhs x)

end Silmaril.Logic.BrookesSC.TreeSC
