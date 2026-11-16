module

public import Silmaril.Logic.Algebraic.Initial.Generation.Thms
public import Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Thms
public import Silmaril.Logic.Algebraic.Initial.Matching.FinitePresented.Thms
public import Silmaril.Logic.Matching.FixedPoint.Simultaneous.Thms

/-! Finite original-sort profiles compiled into native dependent unary fixed
points. The ambient signature, equations, carriers and contextual maps remain
arbitrary. Finiteness is a compiler restriction, not a restriction on Generation. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization
open FixedPoint.Simultaneous

structure Profile where
  sortCount : Nat
  operationCount : Nat
  arity : Fin operationCount → Nat
  input : (c : Fin operationCount) → Fin (arity c) → Fin sortCount
  output : Fin operationCount → Fin sortCount

/-- Each constructor has its original input profile and output coordinate. -/
inductive Operation (D : Profile) :
    (n : Nat) → (Fin n → Fin D.sortCount) → Fin D.sortCount → Type where
  | mk (c : Fin D.operationCount) : Operation D (D.arity c) (D.input c) (D.output c)

def Profile.signature (D : Profile) : EQ.Signature :=
  ⟨Fin D.sortCount, Operation D⟩

abbrev Equations (D : Profile) := ULift.{1} (EQ.Equation D.signature)
def theory (D : Profile) (E : Set (Equations D)) : Initial.Theory := ⟨D.signature, E⟩

abbrev coordinate {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) :=
  GuardedFOL.MatchingSort.object (S := SignedSpectrum.folSignature B) (σ.sorts i)

abbrev emptyContext {B : EQ.Signature} :
    Fin 0 → (SignedSpectrum.nativeSignature B).sorts := fun i => i.elim0

abbrev BodyPat {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) :=
  FixedPoint.Pattern (SignedSpectrum.nativeSignature B).symbols
    (append (coordinate σ) (emptyContext (B := B))) (emptyContext (B := B)) (coordinate σ i)

abbrev ClosedPat {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) :=
  FixedPoint.Pattern (SignedSpectrum.nativeSignature B).symbols
    (emptyContext (B := B)) (emptyContext (B := B)) (coordinate σ i)

def bottom {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) : BodyPat σ i :=
  .base (.conj (.ex (coordinate σ i) (.var 0))
    (.neg (.ex (coordinate σ i) (.var 0))))

def disjunction {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) : List (BodyPat σ i) → BodyPat σ i
  | [] => bottom σ i
  | p :: ps => .disj p (disjunction σ i ps)

/-- Selection is decided in the ORIGINAL coordinate family, before applying σ. -/
def operationsAt (D : Profile) (i : Fin D.sortCount) :
    List {c : Fin D.operationCount // D.output c = i} :=
  (List.finRange D.operationCount).filterMap fun c =>
    if h : D.output c = i then some ⟨c, h⟩ else none

/-- A recursive variable retains its original coordinate through the compiler's
explicit append interface. -/
def recursionVariable {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) : BodyPat σ i :=
  by
    change FixedPoint.Pattern (SignedSpectrum.nativeSignature B).symbols
      (append (coordinate σ) (emptyContext (B := B))) (emptyContext (B := B))
      (coordinate σ i)
    exact (append_left (coordinate σ) (emptyContext (B := B)) i) ▸
      (.setvar (Fin.castAdd 0 i) :
        FixedPoint.Pattern (SignedSpectrum.nativeSignature B).symbols
          (append (coordinate σ) (emptyContext (B := B))) (emptyContext (B := B))
          (append (coordinate σ) (emptyContext (B := B)) (Fin.castAdd 0 i)))

/-- Every argument predicate refers to its original input coordinate, even
when σ identifies some input/output sorts or operation symbols. -/
def constructorPattern {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (c : Fin D.operationCount) : BodyPat σ (D.output c) :=
  .app (.function (σ.ops (Operation.mk c)))
    (fun j => recursionVariable σ (D.input c j))

def body {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) : BodyPat σ i :=
  disjunction σ i ((operationsAt D i).map
    fun (c : {c : Fin D.operationCount // D.output c = i}) =>
      Eq.mp (congrArg (BodyPat σ) c.property) (constructorPattern σ c.val))

def system {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B) :
    System (SignedSpectrum.nativeSignature B).symbols (coordinate σ)
      (emptyContext (B := B)) (emptyContext (B := B)) :=
  ⟨body σ⟩

def generated {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) : ClosedPat σ i :=
  (system σ).compile i

/-- Padding is ignored. No active-carrier inhabitance is required. -/
def generationClause {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (i : Fin D.sortCount) :
    FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols :=
  ⟨0, 0, emptyContext, emptyContext, coordinate σ i,
    .disj (.base (.neg (.app
      (GuardedFOL.Operation.active (S := SignedSpectrum.folSignature B) (σ.sorts i))
      (fun j => j.elim0)))) (generated σ i)⟩

/-- Arbitrary original equations and their complete contexts are retained.
No pushforward/reclosure of E is taken after ambient collisions. -/
def compiled {D : Profile} (E : Set (Equations D)) {B : EQ.Signature}
    (σ : D.signature ⟶ B) :
    Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols) :=
  Set.range (generationClause σ) ∪
    FixedPoint.encodeFirstOrder '' SignedSpectrum.spectrum (theory D E) σ

abbrev reduct {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (N : SignedSpectrum.NativeModel B) :=
  (EQ.Algebra.reduct σ).obj (SignedSpectrum.decode N)

abbrev RawFamily {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (N : SignedSpectrum.NativeModel B) :=
  FixedPoint.SetEnv (SignedSpectrum.nativeSignature B).symbols N.base (coordinate σ)

def rawStep {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (N : SignedSpectrum.NativeModel B) : RawFamily σ N →o RawFamily σ N :=
  (system σ).operator N.base (fun i => i.elim0) (fun i => i.elim0)

def embedFamily {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (N : SignedSpectrum.NativeModel B) (X : Generation.Family (reduct σ N)) :
    RawFamily σ N :=
  fun i => Subtype.val '' X i

def extractFamily {D : Profile} {B : EQ.Signature} (σ : D.signature ⟶ B)
    (N : SignedSpectrum.NativeModel B) (X : RawFamily σ N) :
    Generation.Family (reduct σ N) :=
  fun i => {a | a.val ∈ X i}

def actual {D : Profile} (E : Set (Equations D)) {B : EQ.Signature}
    (σ : D.signature ⟶ B) : Initial.Constraint B :=
  Silmaril.Logic.Institution.Structured.Constraints.translate Initial.equational σ
    (Initial.initialConstraint (theory D E))

abbrev Satisfies {B : EQ.Signature} (N : SignedSpectrum.NativeModel B)
    (H : Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols)) :=
  PresentedCompiler.Satisfies N H

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler
