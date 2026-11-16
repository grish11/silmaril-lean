module

public import Silmaril.Logic.Algebraic.Initial.Matching.Presented.Thms
public import Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Thms
public import Silmaril.Logic.Matching.FixedPoint.Thms

/-! Finite one-sort presented initiality without a nullary or inhabitance
assumption. The original equations and full contexts are retained under arbitrary
ambient contextual signature maps. Empty generated active carriers are permitted. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching

/-- A finite operation profile, including zero operations and signatures with no constants. -/
structure Profile where
  count : Nat
  arity : Fin count → Nat

def Profile.signature (D : Profile) : EQ.Signature :=
  ⟨Unit, fun n _ _ => {c : Fin D.count // D.arity c = n}⟩

/-- Forget only the legacy profile's selected nullary witness. -/
def Profile.ofConstructors (D : Constructors) : Profile := ⟨D.count, D.arity⟩

theorem Profile.ofConstructors_signature (D : Constructors) :
    (Profile.ofConstructors D).signature = D.signature.public := rfl

inductive Tree (D : Profile) where
  | node (constructor : Fin D.count) (arguments : Fin (D.arity constructor) → Tree D)

def fold (D : Profile) (M : EQ.Algebra D.signature) : Tree D → M.carrier ()
  | .node c args => M.op (w := fun _ => ()) (s := ()) ⟨c, rfl⟩
      (fun i => fold D M (args i))

def treeAlgebra (D : Profile) : EQ.Algebra D.signature where
  carrier _ := Tree D
  op := fun ⟨c, h⟩ args => .node c (fun i => args (Fin.cast h i))

abbrev Equations (D : Profile) := ULift.{1} (EQ.Equation D.signature)

def theory (D : Profile) (E : Set (Equations D)) : Initial.Theory :=
  ⟨D.signature, E⟩

abbrev targetSort {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) :=
  GuardedFOL.MatchingSort.object (S := SignedSpectrum.folSignature B) (σ.sorts ())

abbrev Pat {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (r : Nat) :=
  FixedPoint.Pattern (SignedSpectrum.nativeSignature B).symbols
    (fun _ : Fin r => targetSort σ) (fun _ : Fin 0 => targetSort σ) (targetSort σ)

def bottom {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) {r : Nat} : Pat σ r :=
  .base (.conj (.ex (targetSort σ) (.var 0))
    (.neg (.ex (targetSort σ) (.var 0))))

def disjunction {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) {r : Nat} : List (Pat σ r) → Pat σ r
  | [] => bottom σ
  | p :: ps => .disj p (disjunction σ ps)

def generatedBody {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) : Pat σ 1 :=
  disjunction σ ((List.finRange D.count).map fun c =>
    .app (.function (σ.ops (w := fun _ => ()) (s := ()) ⟨c, rfl⟩))
      (fun _ => .setvar 0))

def generated {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) : Pat σ 0 := .mu (generatedBody σ)

/-- Global coverage of the active object carrier, without constraining padding. -/
def generationClause {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) :
    FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols :=
  ⟨0, 0, (fun _ => targetSort σ), (fun _ => targetSort σ), targetSort σ,
    .disj (.base (.neg (.app (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0))))
      (generated σ)⟩

/-- A native sentence theory, not a single finite equality decision procedure. -/
def compiled {D : Profile} (E : Set (Equations D)) {B : EQ.Signature}
    (σ : D.signature ⟶ B) :
    Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols) :=
  {generationClause σ} ∪
    FixedPoint.encodeFirstOrder '' SignedSpectrum.spectrum (theory D E) σ

/-- The existing initiality constraint, with only its contextual signature changed. -/
def actual {D : Profile} (E : Set (Equations D)) {B : EQ.Signature}
    (σ : D.signature ⟶ B) : Initial.Constraint B :=
  Silmaril.Logic.Institution.Structured.Constraints.translate Initial.equational σ
    (Initial.initialConstraint (theory D E))

abbrev Satisfies {B : EQ.Signature} (N : SignedSpectrum.NativeModel B)
    (H : Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols)) : Prop :=
  PresentedCompiler.Satisfies N H

abbrev reduct {D : Profile} {B : EQ.Signature}
    (σ : D.signature ⟶ B) (N : SignedSpectrum.NativeModel B) :=
  (EQ.Algebra.reduct σ).obj (SignedSpectrum.decode N)

end Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler
