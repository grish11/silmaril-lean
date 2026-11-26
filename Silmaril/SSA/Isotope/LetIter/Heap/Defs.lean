module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Structured.Thms
public import Silmaril.Semantics.ITree.Reindex.Thms
public import Silmaril.Semantics.Reindex.Thms
public import Mathlib.Logic.Equiv.Option

/-! # A typed LetIter heap dialect -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap

open Silmaril.Isotope.Semantics Silmaril.Elgot
open PaperExpression.Source.FreeTree.Response.Structured (Lifted)


inductive Prim where
  | alloc
  | get
  | set
  | free

abbrev refTy : Ty Unit := .base ()
abbrev valueTy : Ty Unit := .coprod .unit refTy

instance : HasTy Prim (Ty Unit) where
  src
    | .alloc => valueTy
    | .get | .free => refTy
    | .set => .product refTy valueTy
  trg
    | .alloc => refTy
    | .get => valueTy
    | .set | .free => .unit

abbrev Carrier (I : Type) : Unit → Type := fun _ => I

/-- Values may contain a reference. The unit payload carries no index. -/
abbrev Value (I : Type) := Ty.denote (Carrier I) valueTy

abbrev Event (I : Type) :=
  PaperExpression.Source.FreeTree.Response.Structured.Event (Φ := Prim) (Carrier I)

abbrev allocEvent {I : Type} (v : Value I) : Event I I :=
  PaperExpression.Source.FreeTree.Response.Structured.Event.call (V := Carrier I) Prim.alloc v

abbrev getEvent {I : Type} (i : I) : Event I (Value I) :=
  PaperExpression.Source.FreeTree.Response.Structured.Event.call (V := Carrier I) Prim.get i

abbrev setEvent {I : Type} (i : I) (v : Value I) : Event I PUnit :=
  PaperExpression.Source.FreeTree.Response.Structured.Event.call (V := Carrier I) Prim.set (i, v)

abbrev freeEvent {I : Type} (i : I) : Event I PUnit :=
  PaperExpression.Source.FreeTree.Response.Structured.Event.call (V := Carrier I) Prim.free i

/-- Heap values at the universe of the native evaluator. -/
abbrev EvalType (I : Type) := Ty.denote (Lifted (Carrier I))

/-- LetIter's direct monadic evaluator invokes these typed requests. The
heap handler separately determines which replies are admissible. -/
def instructions (I : Type) : InstructionModel (EvalType I) Prim (ITree.Tree (Event I)) :=
  Reindex.Structured.callInstructions (Carrier I)

/-- A partial store. Its live domain consists of the indices with a value. -/
abbrev Store (I : Type) := I → Option (Value I)

def emptyStore (I : Type) : Store I := fun _ => none

noncomputable def write {I : Type} (s : Store I) (i : I) (v : Option (Value I)) :
    Store I := by
  classical
  exact Function.update s i v

/-- Allocation may return any fresh index. Reads, writes and frees require a
live index. Writes and frees return unit. There is no successful exchange
for an invalid access or an allocation on a full store. -/
def step {I : Type} : ITree.Handler (Store I) (Event I)
  | ⟨_, .call .alloc v⟩, s, i, t => s i = none ∧ t = write s i (some v)
  | ⟨_, .call .get i⟩, s, v, t => s i = some v ∧ t = s
  | ⟨_, .call .set x⟩, s, _, t => s x.1 ≠ none ∧ t = write s x.1 (some x.2)
  | ⟨_, .call .free i⟩, s, _, t => s i ≠ none ∧ t = write s i none

variable {I J : Type}

def valueEquiv (e : I ≃ J) : Value I ≃ Value J := Equiv.sumCongr (Equiv.refl _) e

def storeEquiv (e : I ≃ J) : Store I ≃ Store J :=
  Reindex.function e (Equiv.optionCongr (valueEquiv e))

/-- Representation change for the evaluator's entire type grammar. -/
def resultEquiv (e : I ≃ J) (A : Ty Unit) : EvalType I A ≃ EvalType J A :=
  Reindex.typeEquiv (Reindex.Structured.liftedEquiv (fun _ => e)) A

def signatureEquiv (e : I ≃ J) : ITree.SignatureEquiv (Event I) (Event J) :=
  Reindex.Structured.signatureEquiv (fun _ => e)

def renameRequest (e : I ≃ J) : ITree.Request (Event I) → ITree.Request (Event J) :=
  (signatureEquiv e).request

theorem renameRequest_inverse (e : I ≃ J) (q : ITree.Request (Event I)) :
    renameRequest e.symm (renameRequest e q) = q :=
  Reindex.Structured.request_inverse (fun _ => e) q

end Silmaril.Isotope.LetIter.Heap
