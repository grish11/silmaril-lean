module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Defs
public import Silmaril.Semantics.ITree.Reindex.Thms
public import Silmaril.Semantics.Reindex.Thms
public import Mathlib.Logic.Equiv.Option

/-! # A typed LetIter heap dialect -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap

open Silmaril.Isotope.Semantics Silmaril.Elgot
open PaperExpression.Source.FreeTree.Response.Structured (toSmall)


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

/-- LetIter's direct monadic evaluator invokes these typed requests. The
heap handler separately determines which replies are admissible. -/
def instructions (I : Type) :
    InstructionModel (Ty.denote (fun _ : Unit => ULift.{1} I)) Prim (ITree.Tree (Event I)) where
  eval f x :=
    ITree.vis (.call f (toSmall (Carrier I) (instrSrc f) x))
      (fun r => ITree.ret ((toSmall (Carrier I) (instrTrg f)).symm r))

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

def renameRequest (e : I ≃ J) : ITree.Request (Event I) → ITree.Request (Event J)
  | ⟨_, .call .alloc v⟩ => ⟨_, .call .alloc (valueEquiv e v)⟩
  | ⟨_, .call .get i⟩ => ⟨_, .call .get (e i)⟩
  | ⟨_, .call .set x⟩ => ⟨_, .call .set (e x.1, valueEquiv e x.2)⟩
  | ⟨_, .call .free i⟩ => ⟨_, .call .free (e i)⟩

theorem renameRequest_inverse (e : I ≃ J) (q : ITree.Request (Event I)) :
    renameRequest e.symm (renameRequest e q) = q := by
  rcases q with ⟨_, ⟨f, x⟩⟩
  have h : (valueEquiv e.symm : Value J ≃ Value I) = (valueEquiv e).symm := rfl
  cases f
  · change Value I at x
    exact congrArg (fun v : Value I => (⟨I, allocEvent v⟩ : ITree.Request (Event I)))
      (h.symm ▸ (valueEquiv e).symm_apply_apply x)
  · change I at x
    exact congrArg (fun i : I => (⟨Value I, getEvent i⟩ : ITree.Request (Event I)))
      (e.symm_apply_apply x)
  · change I × Value I at x
    obtain ⟨i, v⟩ := x
    have hi := e.symm_apply_apply i
    have hv : valueEquiv e.symm (valueEquiv e v) = v :=
      h.symm ▸ (valueEquiv e).symm_apply_apply v
    exact congrArg₂ (fun i : I => fun v : Value I =>
      (⟨PUnit, setEvent i v⟩ : ITree.Request (Event I))) hi hv
  · change I at x
    exact congrArg (fun i : I => (⟨PUnit, freeEvent i⟩ : ITree.Request (Event I)))
      (e.symm_apply_apply x)

def signatureEquiv (e : I ≃ J) : ITree.SignatureEquiv (Event I) (Event J) where
  request := ⟨renameRequest e, renameRequest e.symm, renameRequest_inverse e,
    fun q => by simpa only [Equiv.symm_symm] using renameRequest_inverse e.symm q⟩
  reply
    | ⟨_, .call .alloc _⟩ => e
    | ⟨_, .call .get _⟩ => valueEquiv e
    | ⟨_, .call .set _⟩ | ⟨_, .call .free _⟩ => Equiv.refl _

end Silmaril.Isotope.LetIter.Heap
