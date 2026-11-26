module

public import Silmaril.Logic.ITree.Institution.Trace.Thms
public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Clock.Defs
public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Thms

/-! # Heap and clock examples for the finite trace institution -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Heap.TraceExamples

open CategoryTheory Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree.TraceInstitution (Sentence)

abbrev heap (I : Type) : TraceSignature := ⟨heapSignature I⟩

def rename {I J : Type} (e : I ≃ J) : heap I ⟶ heap J :=
  TraceSignature.ofEquiv (signatureEquiv e)

abbrev clock : TraceSignature := ⟨clockSignature⟩

abbrev heapClock (I : Type) : TraceSignature := ⟨(heapSignature I).sum clockSignature⟩

def heapInclusion (I : Type) : heap I ⟶ heapClock I :=
  TraceSignature.inl (heapSignature I) clockSignature

def clockInclusion (I : Type) : clock ⟶ heapClock I :=
  TraceSignature.inr (heapSignature I) clockSignature

/-- A heap observation contains neither a pending tick nor a completed tick. -/
def noClock {I A : Type} : Trace (heapClock I).toSignature.Event A → Prop
  | .request (.inr _) | .exchange (.inr _) _ _ => False
  | .exchange (.inl _) _ tail => noClock tail
  | _ => True

/-- Attempt one allocation and discard the pointer if the handler replies. -/
def allocOnce (I : Type) : Sentence.{0,0} (heap I) :=
  ⟨PUnit, vis (allocEvent (.inl PUnit.unit)) (fun _ => ret PUnit.unit), fun _ => True⟩

/-- Request a clock tick and discard its reply, giving the same return type as allocation. -/
def tickOnce : Sentence.{0,0} clock :=
  ⟨PUnit, vis Clock.tick (fun _ => ret PUnit.unit), fun _ => True⟩

end Silmaril.Isotope.LetIter.Heap.TraceExamples
