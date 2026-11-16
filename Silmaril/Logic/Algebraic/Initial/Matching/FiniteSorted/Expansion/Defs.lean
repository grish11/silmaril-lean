module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Institution.Thms
public import Silmaril.Logic.Institution.Structured.Constraints.Isomorphism.Thms
public import Silmaril.Logic.Institution.Faithful

/-! Actual guarded expansion for the finite-source global comparison.
An expansion decodes to an isomorphic algebra, including at empty carriers.
Neither literal object equality nor a validity certificate is stored. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching

/-- The actual source model, with no relation interpretations added. -/
def expandModel {B : EQ.Signature} (M : EQ.Algebra B) : SignedSpectrum.NativeModel B :=
  GuardedFOL.expand (SignedSpectrum.structureOf M)

/-- Forget only relation data; all carrier maps and operation laws remain. -/
def forgetRelations (B : EQ.Signature) :
    FOL.Structure (SignedSpectrum.folSignature B) ⥤ EQ.Algebra B where
  obj M := M.toAlgebra
  map h := ⟨h.map, h.map_op⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The existing actual FOL expansion iso, mapped to the EQ algebra category. -/
def decodeExpandIso {B : EQ.Signature} (M : EQ.Algebra B) :
    SignedSpectrum.decode (expandModel M) ≅ M :=
  (forgetRelations B).mapIso (GuardedFOL.decodeExpansionIso (SignedSpectrum.structureOf M))

/-- Every actual source homomorphism lifts between the chosen expansions. -/
def expandHom {B : EQ.Signature} {M N : EQ.Algebra B} (h : M ⟶ N) :
    expandModel M ⟶ expandModel N :=
  liftDecodedHom ((decodeExpandIso M).hom ≫ h ≫ (decodeExpandIso N).inv)

/-- Satisfiability of an arbitrary set of original finite presentation sentences. -/
def SourceSatisfiable {B : EQ.Signature} (H : Set (Sentence B)) : Prop :=
  ∃ M : EQ.Algebra B, ∀ p ∈ H, p.Satisfies M

/-- Satisfiability in the actual target model category of native clause theories. -/
def TargetSatisfiable {B : EQ.Signature} (K : Set (TheorySentence B)) : Prop :=
  ∃ N : SignedSpectrum.NativeModel B, ∀ q ∈ K, (theoryRoom B).Sat N q

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
