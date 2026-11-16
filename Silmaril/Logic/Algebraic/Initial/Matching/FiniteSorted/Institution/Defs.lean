module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Naturality.Thms
public import Silmaril.Logic.Matching.GuardedFOL.FixedPoint.Thms
public import Silmaril.Logic.Institution.SetSentences.Defs

set_option backward.isDefEq.respectTransparency false

/-! Theory-valued global compilation over the full ambient EQ signature category.
Original finite profiles and equation sets stay fixed under postcomposition.
Models and all actual model arrows are retained; only target sentences are lifted. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Silmaril.Logic.Institution.Structured
open Silmaril.Logic.Institution

/-- The original presentation is data, not an asserted validity certificate. -/
structure Sentence (B : EQ.Signature) : Type 1 where
  profile : Profile
  equations : Set (Equations profile)
  context : profile.signature ⟶ B

def Sentence.map {B C : EQ.Signature} (f : B ⟶ C) (p : Sentence B) : Sentence C :=
  { p with context := p.context ≫ f }

def Sentence.actual {B : EQ.Signature} (p : Sentence B) : Initial.Constraint B :=
  FiniteSortedCompiler.actual p.equations p.context

def Sentence.Satisfies {B : EQ.Signature} (M : EQ.Algebra B) (p : Sentence B) : Prop :=
  Constraints.Sat Initial.equational M p.actual

private theorem noRel_hom_ext {B C : EQ.Signature}
    (f g : SignedSpectrum.folSignature B ⟶ SignedSpectrum.folSignature C)
    (h : f.toHom = g.toHom) : f = g := by
  cases f with
  | mk fh fr =>
    cases g with
    | mk gh gr =>
      cases h
      have hr : @fr = @gr := by
        funext n w rel
        exact rel.elim
      cases hr
      rfl

theorem folMap_id (B : EQ.Signature) :
    SignedSpectrum.folMap (𝟙 B) = 𝟙 (SignedSpectrum.folSignature B) :=
  noRel_hom_ext _ _ rfl

theorem folMap_comp {B C E : EQ.Signature} (f : B ⟶ C) (g : C ⟶ E) :
    SignedSpectrum.folMap (f ≫ g) = SignedSpectrum.folMap f ≫ SignedSpectrum.folMap g :=
  noRel_hom_ext _ _ rfl

/-- No relation symbols or extra signature morphism restrictions are introduced. -/
def folSignatures : EQ.Signature ⥤ FOL.Signature where
  obj := SignedSpectrum.folSignature
  map := SignedSpectrum.folMap
  map_id := folMap_id
  map_comp := folMap_comp

def nativeSignatures : EQ.Signature ⥤ SortMaps.Signature :=
  folSignatures ⋙ GuardedFOL.signatures

/-- Every decoded FOL homomorphism gives its actual underlying algebra arrow. -/
def decodeModels (B : EQ.Signature) : SignedSpectrum.NativeModel B ⥤ EQ.Algebra B where
  obj := SignedSpectrum.decode
  map h := ⟨h.map, h.map_op⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every algebra arrow between decoded objects lifts, since relation cases are empty. -/
def liftDecodedHom {B : EQ.Signature} {N P : SignedSpectrum.NativeModel B}
    (h : SignedSpectrum.decode N ⟶ SignedSpectrum.decode P) : N ⟶ P where
  map := h.map
  map_op := h.map_op
  map_rel rel := rel.elim

def nativeReduct {B C : EQ.Signature} (f : B ⟶ C) :
    SignedSpectrum.NativeModel C ⥤ SignedSpectrum.NativeModel B :=
  GuardedFOL.reductFunctor (SignedSpectrum.folMap f)

/-- All native μ/ν sentences, including those outside the compiler image. -/
def nativeInstitution : EQ.Signature ⥤ Room.{0,0,1} :=
  folSignatures ⋙ GuardedFOL.fixedInstitution

/-- Arbitrary conjunctions preserve every model object and model arrow. -/
def nativeSetInstitution : EQ.Signature ⥤ Room.{0,0,1} :=
  SetSentences.institution nativeInstitution

/-- The source stores Type-1 equations. Lift target sentences alone to match
that sentence universe; the actual native model category is unchanged. -/
abbrev TheorySentence (B : EQ.Signature) : Type 1 :=
  ULift.{1} (Set (FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols))

def theoryRoom (B : EQ.Signature) : Room.{1,0,1} :=
  ⟨TheorySentence B, (nativeSetInstitution.obj B).Mod,
    fun N Γ => (nativeSetInstitution.obj B).Sat N Γ.down⟩

def theoryCorridor {B C : EQ.Signature} (f : B ⟶ C) : theoryRoom B ⟶ theoryRoom C :=
  ⟨(fun Γ => ULift.up ((nativeSetInstitution.map f).sen Γ.down)),
    (nativeSetInstitution.map f).mod,
    fun N Γ => (nativeSetInstitution.map f).sat N Γ.down⟩

def sourceRoom (B : EQ.Signature) : Room.{1,0,1} :=
  ⟨Sentence B, Cat.of (EQ.Algebra B), Sentence.Satisfies⟩

def Sentence.compile {B : EQ.Signature} (p : Sentence B) : TheorySentence B :=
  ULift.up (compiled p.equations p.context)

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
