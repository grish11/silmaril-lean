module

public import Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open FinitePresentedCompiler

private theorem pattern_transport_heq {S : Type} {A : SortMaps.SortedSignature S}
    {k : Nat} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : FirstOrder.Pattern A Γ s) : HEq (h ▸ p : FirstOrder.Pattern A Δ s) p := by
  cases h
  rfl

private theorem variable_heq {S : Type} {A : SortMaps.SortedSignature S}
    {k : Nat} {Γ Δ : Fin k → S} (h : Γ = Δ) (i : Fin k) :
    HEq (FirstOrder.Pattern.var i : FirstOrder.Pattern A Γ (Γ i))
      (FirstOrder.Pattern.var i : FirstOrder.Pattern A Δ (Δ i)) := by
  cases h
  rfl

theorem bottom_map {D : FinitePresentedCompiler.Profile} {B C : EQ.Signature}
    (σ : D.signature ⟶ B) (f : B ⟶ C) {r : Nat} :
    SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (FinitePresentedCompiler.bottom σ : FinitePresentedCompiler.Pat σ r) =
      (FinitePresentedCompiler.bottom (σ ≫ f) : FinitePresentedCompiler.Pat (σ ≫ f) r) := by
  let m := SignedSpectrum.nativeMap f
  let Γ : Fin 0 → (SignedSpectrum.nativeSignature B).sorts := fun _ => FinitePresentedCompiler.targetSort σ
  have hv :
      ((SortMaps.Hom.map_cons m (FinitePresentedCompiler.targetSort σ) Γ) ▸
        (FirstOrder.Pattern.var 0 :
          FirstOrder.Pattern (SignedSpectrum.nativeSignature C).symbols
            (m.sorts ∘ Fin.cases (FinitePresentedCompiler.targetSort σ) Γ) (m.sorts (FinitePresentedCompiler.targetSort σ)))) =
      (FirstOrder.Pattern.var 0 :
        FirstOrder.Pattern (SignedSpectrum.nativeSignature C).symbols
          (Fin.cases (m.sorts (FinitePresentedCompiler.targetSort σ)) (m.sorts ∘ Γ)) (m.sorts (FinitePresentedCompiler.targetSort σ))) := by
    exact eq_of_heq
      ((pattern_transport_heq (SortMaps.Hom.map_cons m (FinitePresentedCompiler.targetSort σ) Γ) _).trans
        (variable_heq (SortMaps.Hom.map_cons m (FinitePresentedCompiler.targetSort σ) Γ) 0))
  simp only [FinitePresentedCompiler.bottom, SortMaps.Hom.fixedPattern, SortMaps.Hom.pattern]
  simp only [hv]
  rfl

theorem disjunction_map {D : FinitePresentedCompiler.Profile} {B C : EQ.Signature}
    (σ : D.signature ⟶ B) (f : B ⟶ C) {r : Nat} (ps : List (FinitePresentedCompiler.Pat σ r)) :
    SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (FinitePresentedCompiler.disjunction σ ps) =
      FinitePresentedCompiler.disjunction (σ ≫ f)
        (ps.map (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f))) := by
  induction ps with
  | nil => exact bottom_map σ f
  | cons p ps ih =>
    change
      (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) p).disj
        (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f)
          (FinitePresentedCompiler.disjunction σ ps)) =
      (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) p).disj
        (FinitePresentedCompiler.disjunction (σ ≫ f)
          (ps.map (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f))))
    exact congrArg
      (FixedPoint.Pattern.disj (SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) p)) ih

theorem generatedBody_map {D : FinitePresentedCompiler.Profile} {B C : EQ.Signature}
    (σ : D.signature ⟶ B) (f : B ⟶ C) :
    SortMaps.Hom.fixedPattern (SignedSpectrum.nativeMap f) (FinitePresentedCompiler.generatedBody σ) =
      FinitePresentedCompiler.generatedBody (σ ≫ f) := by
  unfold FinitePresentedCompiler.generatedBody
  rw [disjunction_map]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro c hc
  rfl

theorem generationClause_map {D : FinitePresentedCompiler.Profile} {B C : EQ.Signature}
    (σ : D.signature ⟶ B) (f : B ⟶ C) :
    SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f)
        (FinitePresentedCompiler.generationClause σ) =
      FinitePresentedCompiler.generationClause (σ ≫ f) := by
  let m := SignedSpectrum.nativeMap f
  let ΓB : Fin 0 → (SignedSpectrum.nativeSignature B).sorts :=
    fun _ => FinitePresentedCompiler.targetSort σ
  let ΓC : Fin 0 → (SignedSpectrum.nativeSignature C).sorts :=
    fun _ => FinitePresentedCompiler.targetSort (σ ≫ f)
  have hargs :
      (fun i : Fin 0 => SortMaps.Hom.pattern m
        (i.elim0 : FirstOrder.Pattern (SignedSpectrum.nativeSignature B).symbols ΓB
          GuardedFOL.MatchingSort.truth)) =
      (fun i : Fin 0 =>
        (i.elim0 : FirstOrder.Pattern (SignedSpectrum.nativeSignature C).symbols ΓC
          GuardedFOL.MatchingSort.truth)) := by
    funext i
    exact i.elim0
  have hgen :
      SortMaps.Hom.fixedPattern m (FinitePresentedCompiler.generated σ) =
        FinitePresentedCompiler.generated (σ ≫ f) := by
    change (SortMaps.Hom.fixedPattern m (FinitePresentedCompiler.generatedBody σ)).mu =
      (FinitePresentedCompiler.generatedBody (σ ≫ f)).mu
    rw [generatedBody_map]
  change
    (⟨0, 0, ΓC, ΓC, FinitePresentedCompiler.targetSort (σ ≫ f),
      .disj (.base (.neg (.app (GuardedFOL.Operation.active
        (S := SignedSpectrum.folSignature C) ((σ ≫ f).sorts ()))
        (fun i : Fin 0 => SortMaps.Hom.pattern m
          (i.elim0 : FirstOrder.Pattern (SignedSpectrum.nativeSignature B).symbols ΓB
            GuardedFOL.MatchingSort.truth)))))
        (SortMaps.Hom.fixedPattern m (FinitePresentedCompiler.generated σ))⟩ : Atom C) =
    ⟨0, 0, ΓC, ΓC, FinitePresentedCompiler.targetSort (σ ≫ f),
      .disj (.base (.neg (.app (GuardedFOL.Operation.active
        (S := SignedSpectrum.folSignature C) ((σ ≫ f).sorts ()))
        (fun i : Fin 0 => i.elim0))))
        (FinitePresentedCompiler.generated (σ ≫ f))⟩
  rw [hgen, hargs]

theorem encode_map {B C : EQ.Signature} (f : B ⟶ C) (q : SignedSpectrum.NativeSentence B) :
    SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) (FixedPoint.encodeFirstOrder q) =
      FixedPoint.encodeFirstOrder (SortMaps.Hom.sentence (SignedSpectrum.nativeMap f) q) := by
  exact (congrArg (fun c => c.sen q)
    (SortMaps.firstOrderNatural.naturality (SignedSpectrum.nativeMap f))).symm

/-- The original signed kernel is transported, never recomputed in the ambient signature. -/
theorem compiled_map {D : FinitePresentedCompiler.Profile} (E : Set (FinitePresentedCompiler.Equations D)) {B C : EQ.Signature}
    (σ : D.signature ⟶ B) (f : B ⟶ C) :
    SortMaps.Hom.fixedSentence (SignedSpectrum.nativeMap f) '' FinitePresentedCompiler.compiled E σ =
      FinitePresentedCompiler.compiled E (σ ≫ f) := by
  unfold FinitePresentedCompiler.compiled
  rw [Set.image_union, Set.image_singleton, generationClause_map,
    SignedSpectrum.spectrum_map, Set.image_image, Set.image_image]
  congr 1
  apply congrArg (fun g => g '' SignedSpectrum.spectrum (FinitePresentedCompiler.theory D E) σ)
  funext q
  exact encode_map f q

theorem compile_map {B C : EQ.Signature} (f : B ⟶ C) (p : Sentence B) :
    compile (translate f p) = (nativeCorridor f).sen '' compile p := by
  unfold compile translate
  rw [← compiled_map p.equations p.context f, Set.image_image, Set.image_image]
  rfl

def compilerCorridor (B : EQ.Signature) : source.obj B ⟶ target.obj B :=
  ⟨compile, decodeFunctor B, compile_actual_satisfaction⟩

/-- Full signature, sentence and model naturality; the model square is strict
on both objects and arrows. No naturality of chosen expansions is used. -/
def compilerNatural : source ⟶ (𝟭 EQ.Signature) ⋙ target where
  app := compilerCorridor
  naturality := by
    intro B C f
    apply Room.hom_ext
    · funext p
      exact compile_map f p
    · exact (decode_reduct_square f).symm

def sourceInst : Inst.{1,0,1,0,1} := ⟨EQ.Signature, source⟩
def targetInst : Inst.{1,0,1,0,1} := ⟨EQ.Signature, target⟩

/-- Selected finite presented initiality compiles to a possibly infinite native theory. -/
def compiler : Inst.CoHom sourceInst targetInst := ⟨𝟭 _, compilerNatural⟩

/-- Since both signature categories are the same, the same corridor is also
the reversed institution morphism; it is not an inverse translation. -/
def compilerHom : Inst.Hom targetInst sourceInst := ⟨𝟭 _, compilerNatural⟩

def forgetStructure (B : EQ.Signature) :
    FOL.Structure (SignedSpectrum.folSignature B) ⥤ EQ.Algebra B where
  obj M := M.toAlgebra
  map h := h.toAlgebraHom

def expandModel {B : EQ.Signature} (M : EQ.Algebra B) : NativeModel B :=
  GuardedFOL.expand (SignedSpectrum.structureOf M)

/-- Actual public algebra isomorphism, not literal carrier equality. -/
def decodeExpansionIso {B : EQ.Signature} (M : EQ.Algebra B) :
    SignedSpectrum.decode (expandModel M) ≅ M :=
  (forgetStructure B).mapIso (GuardedFOL.decodeExpansionIso (SignedSpectrum.structureOf M))

theorem compiler_isoExpansive (B : EQ.Signature) :
    Corridor.IsoExpansive (compilerCorridor B) :=
  fun M => ⟨expandModel M, ⟨decodeExpansionIso M⟩⟩

end Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented
