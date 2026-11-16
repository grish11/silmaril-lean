module

public import Silmaril.Logic.Algebraic.Initial.Matching.Algebra
public import Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Thms
public import Silmaril.Logic.Matching.FixedPoint.Thms

/-! Native initiality theories for a finite one-sort constructor signature and
arbitrary original equations. The reused `Constructors` profile includes a
selected nullary constructor. Ambient signatures and contextual maps are arbitrary.
The active-domain clause ignores raw padding; the signed spectrum retains the
original presentation and every equation context. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.PresentedCompiler
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching

abbrev Equations (D : Constructors) := ULift.{1} (EQ.Equation D.signature.public)

def theory (D : Constructors) (E : Set (Equations D)) : Initial.Theory :=
  ⟨D.signature.public, E⟩

abbrev targetSort {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) :=
  GuardedFOL.MatchingSort.object (S := SignedSpectrum.folSignature B) (σ.sorts ())

abbrev Pat {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (r : Nat) :=
  FixedPoint.Pattern (SignedSpectrum.nativeSignature B).symbols
    (fun _ : Fin r => targetSort σ) (fun _ : Fin 0 => targetSort σ) (targetSort σ)

def bottom {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) {r : Nat} : Pat σ r :=
  .base (.conj (.ex (targetSort σ) (.var 0))
    (.neg (.ex (targetSort σ) (.var 0))))

def disjunction {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) {r : Nat} : List (Pat σ r) → Pat σ r
  | [] => bottom σ
  | p :: ps => .disj p (disjunction σ ps)

def generatedBody {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) : Pat σ 1 :=
  disjunction σ ((List.finRange D.count).map fun c =>
    .app (.function (σ.ops (w := fun _ => ()) (s := ()) ⟨c, rfl⟩))
      (fun _ => .setvar 0))

def generated {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) : Pat σ 0 := .mu (generatedBody σ)

/-- Global coverage of the active object carrier, without constraining padding. -/
def generationClause {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) :
    FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols :=
  ⟨0, 0, (fun _ => targetSort σ), (fun _ => targetSort σ), targetSort σ,
    .disj (.base (.neg (.app (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts ())) (fun i => i.elim0))))
      (generated σ)⟩

/-- A native sentence theory, not a single finite equality decision procedure. -/
def compiled {D : Constructors} (E : Set (Equations D)) {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) :
    Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols) :=
  {generationClause σ} ∪
    FixedPoint.encodeFirstOrder '' SignedSpectrum.spectrum (theory D E) σ

/-- The existing initiality constraint, with only its contextual signature changed. -/
def actual {D : Constructors} (E : Set (Equations D)) {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) : Initial.Constraint B :=
  Silmaril.Logic.Institution.Structured.Constraints.translate Initial.equational σ
    (Initial.initialConstraint (theory D E))

def Satisfies {B : EQ.Signature} (N : SignedSpectrum.NativeModel B)
    (H : Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols)) : Prop :=
  ∀ q ∈ H, q.Satisfies N.base

abbrev reduct {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :=
  (EQ.Algebra.reduct σ).obj (SignedSpectrum.decode N)

end Silmaril.Logic.Algebraic.Initial.Matching.PresentedCompiler
