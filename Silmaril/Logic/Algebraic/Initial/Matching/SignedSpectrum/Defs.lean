module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Characterization.Thms
public import Silmaril.Logic.Matching.GuardedFOL

/-! Complete signed ground equality spectra. This expresses the exact-kernel
condition; generatedness and initiality are separate. The original presentation
is retained under every contextual signature map. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Presented Presented.Characterization

/-- Add no relation symbols to the original, possibly empty-sorted signature. -/
def folSignature (A : EQ.Signature) : FOL.Signature where
  toSignature := A
  Rel := fun _ _ => PEmpty

def folMap {A B : EQ.Signature} (f : A ⟶ B) : folSignature A ⟶ folSignature B where
  toHom := f
  rels r := r.elim

abbrev nativeSignature (A : EQ.Signature) := GuardedFOL.signature (folSignature A)
abbrev NativeSentence (A : EQ.Signature) :=
  Silmaril.Logic.Matching.FirstOrder.Sentence (nativeSignature A).symbols
abbrev NativeModel (A : EQ.Signature) := GuardedFOL.Model (folSignature A)
abbrev nativeMap {A B : EQ.Signature} (f : A ⟶ B) := GuardedFOL.signatureMap (folMap f)

/-- Decode active carriers, which may be empty, and actual operation graphs. -/
abbrev decode {A : EQ.Signature} (N : NativeModel A) : EQ.Algebra A :=
  (GuardedFOL.decode N).toAlgebra

def structureOf {A : EQ.Signature} (M : EQ.Algebra A) : FOL.Structure (folSignature A) where
  toAlgebra := M
  rel r _ := r.elim

/-- Equality is native definedness of the intersection of singleton term graphs. -/
def positive {A B : EQ.Signature} (σ : A ⟶ B) {s : A.S} (a b : Ground A s) :
    NativeSentence B :=
  GuardedFOL.sentence ((⟨closedContext A, .eq a b⟩ : FOL.Sentence (folSignature A)).map (folMap σ))

/-- The negative clause is native pattern negation, not an external truth label. -/
def negative {A B : EQ.Signature} (σ : A ⟶ B) {s : A.S} (a b : Ground A s) :
    NativeSentence B :=
  GuardedFOL.sentence ((⟨closedContext A, .not (.eq a b)⟩ : FOL.Sentence (folSignature A)).map (folMap σ))

/-- A possibly infinite set of finitary native sentences. `Rel T` still requires
complete instances of every declared equation context, including unused variables.
No equality decision procedure, finite presentation, or inhabitance is assumed. -/
def spectrum (T : Theory) {B : EQ.Signature} (σ : T.sig ⟶ B) : Set (NativeSentence B) :=
  {q | (∃ (s : T.sig.S) (a b : Ground T.sig s), Rel T (closedContext T.sig) a b ∧ q = positive σ a b) ∨
    (∃ (s : T.sig.S) (a b : Ground T.sig s), ¬ Rel T (closedContext T.sig) a b ∧ q = negative σ a b)}

def Satisfies {A : EQ.Signature} (N : NativeModel A) (H : Set (NativeSentence A)) : Prop :=
  ∀ q ∈ H, q.Satisfies N.base

end Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum
