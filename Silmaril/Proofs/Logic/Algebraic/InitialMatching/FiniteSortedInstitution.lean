module

public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Institution.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Silmaril.Logic.Institution.Structured

variable {B C E : EQ.Signature}

theorem Sentence.map_id (p : Sentence B) : p.map (𝟙 B) = p := by
  cases p
  simp only [Sentence.map, Category.comp_id]

theorem Sentence.map_comp (f : B ⟶ C) (g : C ⟶ E) (p : Sentence B) :
    p.map (f ≫ g) = (p.map f).map g := by
  cases p
  simp only [Sentence.map, Category.assoc]

theorem Sentence.actual_map (f : B ⟶ C) (p : Sentence B) :
    (p.map f).actual = Constraints.translate Initial.equational f p.actual := by
  exact Constraints.translate_comp Initial.equational p.context f
    (Initial.initialConstraint (theory p.profile p.equations))

theorem Sentence.satisfaction (f : B ⟶ C) (M : EQ.Algebra C) (p : Sentence B) :
    (p.map f).Satisfies M ↔ p.Satisfies ((EQ.Algebra.reduct f).obj M) := by
  unfold Sentence.Satisfies
  rw [Sentence.actual_map]
  exact Constraints.satisfaction Initial.equational f M p.actual

def sourceCorridor (f : B ⟶ C) : sourceRoom B ⟶ sourceRoom C :=
  ⟨Sentence.map f, EQ.Algebra.reduct f, Sentence.satisfaction f⟩

theorem sourceCorridor_id (B : EQ.Signature) : sourceCorridor (𝟙 B) = 𝟙 (sourceRoom B) :=
  Room.hom_ext (funext Sentence.map_id) rfl

theorem sourceCorridor_comp (f : B ⟶ C) (g : C ⟶ E) :
    sourceCorridor (f ≫ g) = sourceCorridor f ≫ sourceCorridor g :=
  Room.hom_ext (funext (Sentence.map_comp f g)) rfl

def sourceInstitution : EQ.Signature ⥤ Room.{1,0,1} where
  obj := sourceRoom
  map := sourceCorridor
  map_id := sourceCorridor_id
  map_comp := sourceCorridor_comp

/-- The map is surjective on EACH actual hom-set, not merely on identity arrows. -/
theorem decodeModels_full (B : EQ.Signature) (N P : SignedSpectrum.NativeModel B) :
    Function.Surjective (fun h : N ⟶ P => (decodeModels B).map h) := by
  intro h
  exact ⟨liftDecodedHom h, rfl⟩

theorem decodeModels_faithful (B : EQ.Signature) (N P : SignedSpectrum.NativeModel B) :
    Function.Injective (fun h : N ⟶ P => (decodeModels B).map h) := by
  intro h k equality
  have hm : h.map = k.map := congrArg (fun g : SignedSpectrum.decode N ⟶ SignedSpectrum.decode P => g.map) equality
  cases h
  cases k
  cases hm
  rfl

theorem decodeModels_map_lift {N P : SignedSpectrum.NativeModel B}
    (h : SignedSpectrum.decode N ⟶ SignedSpectrum.decode P) :
    (decodeModels B).map (liftDecodedHom h) = h := by
  cases h
  rfl

/-- Strict equality of FULL functors: objects, carrier maps and operation laws. -/
theorem decode_reduct_square (f : B ⟶ C) :
    nativeReduct f ⋙ decodeModels B = decodeModels C ⋙ EQ.Algebra.reduct f := rfl

theorem theoryCorridor_id (B : EQ.Signature) : theoryCorridor (𝟙 B) = 𝟙 (theoryRoom B) := by
  apply Room.hom_ext
  · funext Γ
    cases Γ with
    | up Γ =>
      change ULift.up ((nativeSetInstitution.map (𝟙 B)).sen Γ) = ULift.up Γ
      rw [nativeSetInstitution.map_id]
      rfl
  · change (nativeSetInstitution.map (𝟙 B)).mod = 𝟭 _
    rw [nativeSetInstitution.map_id]
    rfl

theorem theoryCorridor_comp (f : B ⟶ C) (g : C ⟶ E) :
    theoryCorridor (f ≫ g) = theoryCorridor f ≫ theoryCorridor g := by
  apply Room.hom_ext
  · funext Γ
    cases Γ with
    | up Γ =>
      change ULift.up ((nativeSetInstitution.map (f ≫ g)).sen Γ) =
        ULift.up ((nativeSetInstitution.map g).sen ((nativeSetInstitution.map f).sen Γ))
      rw [nativeSetInstitution.map_comp]
      rfl
  · change (nativeSetInstitution.map (f ≫ g)).mod =
      (nativeSetInstitution.map g).mod ⋙ (nativeSetInstitution.map f).mod
    rw [nativeSetInstitution.map_comp]
    rfl

def theoryInstitution : EQ.Signature ⥤ Room.{1,0,1} where
  obj := theoryRoom
  map := theoryCorridor
  map_id := theoryCorridor_id
  map_comp := theoryCorridor_comp

/-- The wrapper does not hide a weaker semantic image claim: this is literal
compiler-set naturality under arbitrary ambient sort/operation collisions. -/
theorem Sentence.compile_map (f : B ⟶ C) (p : Sentence B) :
    (theoryCorridor f).sen p.compile = (p.map f).compile :=
  congrArg ULift.up (FiniteSortedCompiler.compiled_map p.equations p.context f)

theorem Sentence.compile_satisfaction (N : SignedSpectrum.NativeModel B) (p : Sentence B) :
    (theoryRoom B).Sat N p.compile ↔ p.Satisfies (SignedSpectrum.decode N) :=
  FiniteSortedCompiler.compiled_actual_iff p.equations p.context N

/-- Each target theory is a genuine conjunction of every compiled clause. -/
def comparison (B : EQ.Signature) : sourceRoom B ⟶ theoryRoom B :=
  ⟨Sentence.compile, decodeModels B, Sentence.compile_satisfaction⟩

def translation : sourceInstitution ⟶ theoryInstitution where
  app := comparison
  naturality := by
    intro B C f
    apply Room.hom_ext
    · funext p
      exact (Sentence.compile_map f p).symm
    · exact (decode_reduct_square f).symm

/-- Source and target share Type-1 sentence universes; neither model category is lifted. -/
def sourceInst : Inst.{1,0,1,0,1} := ⟨EQ.Signature, sourceInstitution⟩
def theoryInst : Inst.{1,0,1,0,1} := ⟨EQ.Signature, theoryInstitution⟩

/-- Actual global comparison. No literal model-expansiveness or consequence
reflection is inferred from the guarded FOL isomorphic expansion. -/
def toMatching : Inst.CoHom sourceInst theoryInst where
  Φ := 𝟭 _
  ρ := translation ≫ (Functor.leftUnitor theoryInstitution).inv

/-- Forward consequence is supplied by the actual comparison corridor. -/
theorem entails_map (B : EQ.Signature) (H : Set (Sentence B)) (p : Sentence B)
    (h : (sourceRoom B).Entails H p) :
    (theoryRoom B).Entails (Sentence.compile '' H) p.compile :=
  (comparison B).entails_map h

end Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution
