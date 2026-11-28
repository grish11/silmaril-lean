module

public import Silmaril.Logic.ITree.Institution.Thms
public import Silmaril.SSA.Isotope.LetIter.Heap.Thms

/-! # The LetIter heap and a read-only view in the handled ITree institution -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap

open CategoryTheory Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model Sentence)

variable {I J : Type}

/-- The signature and model reuse the typed events and handler of the LetIter heap. -/
def heapSignature (I : Type) : ITree.Signature := ⟨Event I⟩

def heapModel (I : Type) : Model.{0,0} (heapSignature I) :=
  ⟨Store I, fun _ => True, step⟩

/-- A signature with only the heap's read operation. -/
inductive Read (I : Type) : Type → Type where
  | get (i : I) : Read I (Value I)

def readSignature (I : Type) : ITree.Signature := ⟨Read I⟩

def readInclusion (I : Type) : readSignature I ⟶ heapSignature I where
  request | ⟨_, Read.get i⟩ => ⟨_, getEvent i⟩
  reply | ⟨_, Read.get _⟩ => id

def heapRename (e : I ≃ J) : heapSignature I ⟶ heapSignature J :=
  ITree.Signature.ofEquiv (signatureEquiv e)

def readRename (e : I ≃ J) : readSignature I ⟶ readSignature J where
  request | ⟨_, Read.get i⟩ => ⟨_, .get (e i)⟩
  reply | ⟨_, Read.get _⟩ => (valueEquiv e).symm

/-- Two successful reads of the same cell agree. -/
def readLaw (i : I) : Sentence.{0,0} (readSignature I) where
  Result := Value I × Value I
  program := ITree.vis (Read.get i) fun v => ITree.vis (Read.get i) fun w => ITree.ret (v, w)
  post r := r.1 = r.2

/-- Allocate, store a self-reference, read it back, and free the cell. The
returned pair makes the read-back constraint on the allocated cell explicit. -/
def lifecycle : Sentence.{0,0} (heapSignature I) where
  Result := I × Value I
  program := ITree.vis (allocEvent (.inl PUnit.unit)) fun i =>
    ITree.vis (setEvent i (.inr i)) fun _ =>
      ITree.vis (getEvent i) fun v =>
        ITree.vis (freeEvent i) fun _ =>
          ITree.ret (i, v)
  post r := r.2 = .inr r.1

end Silmaril.Isotope.LetIter.Heap
