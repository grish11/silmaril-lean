module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Set.Functor
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Thread-indexed trace semantics

`Det` and `Nondet` read the current thread and accumulate output in chronological
order. `ReadOnly` can also inspect the used names. `Alloc` threads the used names
through each branch of sequencing. An empty set has no returning branches.

The trace monoid determines the output equivalences available to the model.
Changing to quotient output preserves results and used sets. Alpha abstraction is
separate and acts jointly on results, used sets, and output at a fixed input.
-/

@[expose] public section

namespace Silmaril.ThreadTrace

universe u

variable {T W V A B : Type u}

abbrev Det (T W : Type u) := ReaderT T (Writer W)
abbrev Nondet (T W : Type u) := ReaderT T (WriterT W SetM)
abbrev ReadOnly (T W : Type u) := ReaderT T (Nondet (Set T) W)
abbrev Alloc (T W : Type u) := ReaderT T (StateT (Set T) (WriterT W SetM))

/-- A returning branch, with the final used names and accumulated output. -/
abbrev Branch (T W A : Type u) := (A × Set T) × W

/-- Observe the returned value and accumulated output at a current thread. -/
def Det.run (x : Det T W A) (t : T) : A × W := (x t).run

def Nondet.run (x : Nondet T W A) (t : T) : Set (A × W) := (x t).run.run

def ReadOnly.run (x : ReadOnly T W A) (t : T) (used : Set T) : Set (A × W) :=
  (x t).run used

def Alloc.run (x : Alloc T W A) (t : T) (used : Set T) : Set (Branch T W A) :=
  (x t used).run.run

/-- Include a deterministic computation as a singleton choice. -/
def singleton (x : Det T W A) : Nondet T W A :=
  fun t => WriterT.mk (pure (x.run t))

/-- Make the used names available to the reader, leaving the computation independent of them. -/
def ignoreUsed (x : Nondet T W A) : ReadOnly T W A := fun t _ => x t

/-- Run a read-only computation, returning the input used names on every branch. -/
def readOnly (x : ReadOnly T W A) : Alloc T W A := fun t used =>
  WriterT.mk ((fun (a, w) => ((a, used), w)) <$> (x t used).run)

section Output

variable [Monoid W] [Monoid V] (q : W →* V)

/-- Change the output monoid, leaving the result untouched. -/
def Det.mapOutput (x : Det T W A) : Det T V A := fun t => (x t).adapt q

def Nondet.mapOutput (x : Nondet T W A) : Nondet T V A := fun t => (x t).adapt q

def ReadOnly.mapOutput (x : ReadOnly T W A) : ReadOnly T V A :=
  fun t used => (x t used).adapt q

def Alloc.mapOutput (x : Alloc T W A) : Alloc T V A := fun t used => (x t used).adapt q

/-- Lift every representative of each quotient branch, holding the result and state fixed. -/
def Alloc.represent (x : Alloc T V A) : Alloc T W A := fun t used =>
  WriterT.mk (show Set (Branch T W A) from
    {b | (b.1, q b.2) ∈ x.run t used})

/-- Close a computation under replacing output by an equal quotient representative. -/
def Alloc.saturate (x : Alloc T W A) : Alloc T W A :=
  Alloc.represent q (Alloc.mapOutput q x)

/-- The class-complete raw computations for `q`. -/
def Complete (T : Type u) (q : W →* V) (A : Type u) :=
  {x : Alloc T W A // Alloc.saturate q x = x}

/-- Project a class-complete computation to its quotient output. -/
def Complete.project (x : Complete T q A) : Alloc T V A := Alloc.mapOutput q x.1

end Output

section Used

variable [Monoid W]

/-- On a valid input, choose every unused name and return it with that name added.
There are no fresh branches when the current thread is absent or all names are used. -/
def fresh : Alloc T W T := fun t used => WriterT.mk
  (show Set (Branch T W T) from
    {b | t ∈ used ∧ b.1.1 ∉ used ∧ b.1.2 = insert b.1.1 used ∧ b.2 = 1})

/-- On inputs containing the current thread, branches grow the used set and cover
both the returned value's support and the output's support. In particular the
current thread is valid at the continuation. Unsuccessful branches impose no conditions. -/
def Alloc.RespectsUsed (resultSupport : A → Set T) (outputSupport : W → Set T)
    (x : Alloc T W A) : Prop :=
  ∀ ⦃t used a final w⦄, t ∈ used → ((a, final), w) ∈ x.run t used →
    used ⊆ final ∧ resultSupport a ⊆ final ∧ outputSupport w ⊆ final

end Used

section Renaming

open scoped Pointwise

variable [Monoid W] [MulDistribMulAction (Equiv.Perm T) W]

/-- Rename the current thread, result, and output of a deterministic computation. -/
def Det.Equivariant [MulAction (Equiv.Perm T) A] (x : Det T W A) : Prop :=
  ∀ (p : Equiv.Perm T) (t : T), p • x.run t = x.run (p • t)

/-- Rename the current thread and each possible result and output. -/
def Nondet.Equivariant [MulAction (Equiv.Perm T) A] (x : Nondet T W A) : Prop :=
  ∀ (p : Equiv.Perm T) (t : T) (b : A × W), p • b ∈ x.run (p • t) ↔ b ∈ x.run t

/-- Rename both reader inputs and each possible result and output. -/
def ReadOnly.Equivariant [MulAction (Equiv.Perm T) A] (x : ReadOnly T W A) : Prop :=
  ∀ (p : Equiv.Perm T) (t : T) (used : Set T) (b : A × W),
    p • b ∈ x.run (p • t) (p • used) ↔ b ∈ x.run t used

/-- Rename inputs and the entire observed branch together. -/
def Alloc.Equivariant [MulAction (Equiv.Perm T) A] (x : Alloc T W A) : Prop :=
  ∀ (p : Equiv.Perm T) (t : T) (used : Set T) (b : Branch T W A),
    p • b ∈ x.run (p • t) (p • used) ↔ b ∈ x.run t used

/-- The permutations available for alpha abstraction fix the current thread and
all previously used names pointwise. -/
abbrev fixing (t : T) (used : Set T) : Subgroup (Equiv.Perm T) :=
  fixingSubgroup (Equiv.Perm T) (insert t used)

/-- Orbits of complete branches at an input, with existing names held fixed. -/
abbrev Alpha (t : T) (used : Set T) (W A : Type u)
    [Monoid W] [MulDistribMulAction (Equiv.Perm T) W] [MulAction (Equiv.Perm T) A] :=
  MulAction.orbitRel.Quotient (fixing t used) (Branch T W A)

def alpha [MulAction (Equiv.Perm T) A] (t : T) (used : Set T) (b : Branch T W A) :
    Alpha t used W A := Quotient.mk'' b

end Renaming

end Silmaril.ThreadTrace
