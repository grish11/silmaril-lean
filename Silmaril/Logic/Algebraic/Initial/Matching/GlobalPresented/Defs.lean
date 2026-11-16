module

public import Silmaril.Logic.Algebraic.Initial.Matching.FinitePresented.Thms
public import Silmaril.Logic.Institution.SetSentences.Thms
public import Silmaril.Logic.Matching.SortMaps.Thms

set_option backward.isDefEq.respectTransparency false

/-! Selected finite presentations over the full ambient EQ signature category.
The original equations (including their full contexts) are retained by maps.
Native atoms are explicitly lifted to Type 1, matching the selected source's
equation-set universe; the target sentences are sets of these lifted atoms.
All models and their full existing categories are unchanged. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Silmaril.Logic.Institution.Structured
open FinitePresentedCompiler

structure Sentence (B : EQ.Signature) where
  profile : Profile
  equations : Set (Equations profile)
  context : profile.signature ⟶ B

def translate {B C : EQ.Signature} (f : B ⟶ C) (p : Sentence B) : Sentence C :=
  { p with context := p.context ≫ f }

def constraint {B : EQ.Signature} (p : Sentence B) : Initial.Constraint B :=
  actual p.equations p.context

theorem constraint_translate {B C : EQ.Signature} (f : B ⟶ C) (p : Sentence B) :
    constraint (translate f p) =
      Constraints.translate Initial.equational f (constraint p) := by
  exact Constraints.translate_comp Initial.equational p.context f
    (Initial.initialConstraint (theory p.profile p.equations))

def sourceRoom (B : EQ.Signature) : Room.{1,0,1} :=
  ⟨Sentence B, Cat.of (EQ.Algebra B),
    fun M p => Constraints.Sat Initial.equational M (constraint p)⟩

def sourceCorridor {B C : EQ.Signature} (f : B ⟶ C) : sourceRoom B ⟶ sourceRoom C :=
  ⟨translate f, EQ.Algebra.reduct f, by
    intro M p
    change Constraints.Sat Initial.equational M (constraint (translate f p)) ↔
      Constraints.Sat Initial.equational ((EQ.Algebra.reduct f).obj M) (constraint p)
    rw [constraint_translate]
    exact Constraints.satisfaction Initial.equational f M (constraint p)⟩

def source : EQ.Signature ⥤ Room.{1,0,1} where
  obj := sourceRoom
  map := sourceCorridor
  map_id B := by
    apply Room.hom_ext
    · funext p
      change translate (𝟙 B) p = p
      cases p
      simp only [translate, Category.comp_id]
    · rfl
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      change translate (f ≫ g) p = translate g (translate f p)
      cases p
      simp only [translate, Category.assoc]
    · rfl

theorem folMap_id (B : EQ.Signature) :
    SignedSpectrum.folMap (𝟙 B) = 𝟙 (SignedSpectrum.folSignature B) := by
  unfold SignedSpectrum.folMap
  congr 1
  funext n inputs r
  exact r.elim

theorem folMap_comp {A B C : EQ.Signature} (f : A ⟶ B) (g : B ⟶ C) :
    SignedSpectrum.folMap (f ≫ g) = SignedSpectrum.folMap f ≫ SignedSpectrum.folMap g := by
  unfold SignedSpectrum.folMap
  congr 1
  funext n inputs r
  exact r.elim

def folSignatures : EQ.Signature ⥤ FOL.Signature where
  obj := SignedSpectrum.folSignature
  map := SignedSpectrum.folMap
  map_id := folMap_id
  map_comp := folMap_comp

def nativeSignatures : EQ.Signature ⥤ SortMaps.Signature :=
  folSignatures ⋙ GuardedFOL.signatures

abbrev Atom (B : EQ.Signature) :=
  FixedPoint.Sentence (SignedSpectrum.nativeSignature B).symbols

/-- All guarded native models, independent of the selected presentation.
No initiality or compiler satisfaction proof is a model field. -/
abbrev NativeModel (B : EQ.Signature) := SignedSpectrum.NativeModel B

def nativeRoom (B : EQ.Signature) : Room.{1,0,1} :=
  ⟨ULift.{1} (Atom B), Cat.of (NativeModel B),
    fun N p => p.down.Satisfies N.base⟩

def nativeCorridor {B C : EQ.Signature} (f : B ⟶ C) : nativeRoom B ⟶ nativeRoom C :=
  ⟨fun p => ⟨SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) p.down⟩,
    GuardedFOL.reductFunctor (SignedSpectrum.folMap f),
    fun N p => SortMaps.Hom.fixedSatisfaction (SignedSpectrum.nativeMap f) N.base p.down⟩

/-- Native fixed-point semantics uses the existing varying-sort transport.
The model arrows are all arrows of the existing guarded model category. -/
def native : EQ.Signature ⥤ Room.{1,0,1} where
  obj := nativeRoom
  map := nativeCorridor
  map_id B := by
    apply Room.hom_ext
    · funext p
      change ULift.up (SortMaps.Hom.fixedSentence (nativeSignatures.map (𝟙 B)) p.down) = p
      rw [nativeSignatures.map_id, SortMaps.Hom.fixedSentence_id]
      cases p
      rfl
    · change GuardedFOL.reductFunctor (SignedSpectrum.folMap (𝟙 B)) = 𝟭 _
      rw [folMap_id, GuardedFOL.reductFunctor_id]
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      change ULift.up (SortMaps.Hom.fixedSentence (nativeSignatures.map (f ≫ g)) p.down) =
        ULift.up (SortMaps.Hom.fixedSentence (nativeSignatures.map g)
          (SortMaps.Hom.fixedSentence (nativeSignatures.map f) p.down))
      rw [nativeSignatures.map_comp, SortMaps.Hom.fixedSentence_comp]
    · change GuardedFOL.reductFunctor (SignedSpectrum.folMap (f ≫ g)) =
        GuardedFOL.reductFunctor (SignedSpectrum.folMap g) ⋙
          GuardedFOL.reductFunctor (SignedSpectrum.folMap f)
      rw [folMap_comp, GuardedFOL.reductFunctor_comp]

def target : EQ.Signature ⥤ Room.{1,0,1} :=
  Silmaril.Logic.Institution.SetSentences.institution native

def decodeFunctor (B : EQ.Signature) : NativeModel B ⥤ EQ.Algebra B where
  obj := SignedSpectrum.decode
  map h := h.toAlgebraHom

/-- Equality of whole functors, including the maps on every model arrow. -/
theorem decode_reduct_square {B C : EQ.Signature} (f : B ⟶ C) :
    GuardedFOL.reductFunctor (SignedSpectrum.folMap f) ⋙ decodeFunctor B =
      decodeFunctor C ⋙ EQ.Algebra.reduct f := rfl

def compile {B : EQ.Signature} (p : Sentence B) : Set (ULift.{1} (Atom B)) :=
  ULift.up '' compiled p.equations p.context

/-- The representation lift adds no mathematical condition to the native theory. -/
theorem compile_satisfaction {B : EQ.Signature} (N : NativeModel B) (p : Sentence B) :
    (target.obj B).Sat N (compile p) ↔
      FinitePresentedCompiler.Satisfies N (compiled p.equations p.context) := by
  constructor
  · intro h q hq
    exact h ⟨q⟩ ⟨q, hq, rfl⟩
  · intro h q hq
    obtain ⟨q, hq, rfl⟩ := hq
    exact h q hq

theorem compile_actual_satisfaction {B : EQ.Signature} (N : NativeModel B) (p : Sentence B) :
    (target.obj B).Sat N (compile p) ↔ (source.obj B).Sat (SignedSpectrum.decode N) p :=
  (compile_satisfaction N p).trans (compiled_actual_iff p.equations p.context N)

end Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented
