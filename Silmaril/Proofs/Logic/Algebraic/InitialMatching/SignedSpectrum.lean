module

public import Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum.Defs

/-! Satisfaction and signature transport for signed ground spectra. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Presented Presented.Characterization

theorem positive_satisfaction {A B : EQ.Signature} (σ : A ⟶ B) (N : NativeModel B)
    {s : A.S} (a b : Ground A s) :
    (positive σ a b).Satisfies N.base ↔
      evaluate ((EQ.Algebra.reduct σ).obj (decode N)) a =
        evaluate ((EQ.Algebra.reduct σ).obj (decode N)) b := by
  unfold positive
  rw [GuardedFOL.sentence_satisfaction, FOL.Sentence.holds_map]
  rfl

theorem negative_satisfaction {A B : EQ.Signature} (σ : A ⟶ B) (N : NativeModel B)
    {s : A.S} (a b : Ground A s) :
    (negative σ a b).Satisfies N.base ↔
      evaluate ((EQ.Algebra.reduct σ).obj (decode N)) a ≠
        evaluate ((EQ.Algebra.reduct σ).obj (decode N)) b := by
  unfold negative
  rw [GuardedFOL.sentence_satisfaction, FOL.Sentence.holds_map]
  rfl

theorem positive_mem {T : Theory} {B : EQ.Signature} (σ : T.sig ⟶ B)
    {s : T.sig.S} {a b : Ground T.sig s} (h : Rel T (closedContext T.sig) a b) :
    positive σ a b ∈ spectrum T σ := Or.inl ⟨s, a, b, h, rfl⟩

theorem negative_mem {T : Theory} {B : EQ.Signature} (σ : T.sig ⟶ B)
    {s : T.sig.S} {a b : Ground T.sig s} (h : ¬ Rel T (closedContext T.sig) a b) :
    negative σ a b ∈ spectrum T σ := Or.inr ⟨s, a, b, h, rfl⟩

/-- Exactly the ground kernel, with no generatedness or modelhood assumption. -/
theorem satisfies_iff_exactGroundKernel {T : Theory} {B : EQ.Signature}
    (σ : T.sig ⟶ B) (N : NativeModel B) :
    Satisfies N (spectrum T σ) ↔
      ExactGroundKernel T ((EQ.Algebra.reduct σ).obj (decode N)) := by
  classical
  constructor
  · intro h s a b
    constructor
    · intro hab
      by_contra unrelated
      exact ((negative_satisfaction σ N a b).mp
        (h _ (negative_mem σ unrelated))) hab
    · intro related
      exact (positive_satisfaction σ N a b).mp (h _ (positive_mem σ related))
  · intro kernel q member
    rcases member with ⟨s, a, b, related, rfl⟩ | ⟨s, a, b, unrelated, rfl⟩
    · exact (positive_satisfaction σ N a b).mpr ((kernel s a b).mpr related)
    · apply (negative_satisfaction σ N a b).mpr
      intro hab
      exact unrelated ((kernel s a b).mp hab)

theorem positive_map {A B C : EQ.Signature} (σ : A ⟶ B) (f : B ⟶ C)
    {s : A.S} (a b : Ground A s) :
    Silmaril.Logic.Matching.SortMaps.Hom.sentence (nativeMap f) (positive σ a b) =
      positive (σ ≫ f) a b := by
  unfold positive
  rw [GuardedFOL.sentence_map, ← FOL.Sentence.map_comp]
  rfl

theorem negative_map {A B C : EQ.Signature} (σ : A ⟶ B) (f : B ⟶ C)
    {s : A.S} (a b : Ground A s) :
    Silmaril.Logic.Matching.SortMaps.Hom.sentence (nativeMap f) (negative σ a b) =
      negative (σ ≫ f) a b := by
  unfold negative
  rw [GuardedFOL.sentence_map, ← FOL.Sentence.map_comp]
  rfl

/-- Only the ambient context changes. In particular the original negative
congruence facts are retained even when `f` identifies operation symbols. -/
theorem spectrum_map {T : Theory} {B C : EQ.Signature} (σ : T.sig ⟶ B) (f : B ⟶ C) :
    spectrum T (σ ≫ f) =
      Silmaril.Logic.Matching.SortMaps.Hom.sentence (nativeMap f) '' spectrum T σ := by
  ext q
  constructor
  · rintro (⟨s, a, b, related, rfl⟩ | ⟨s, a, b, unrelated, rfl⟩)
    · exact ⟨positive σ a b, positive_mem σ related, positive_map σ f a b⟩
    · exact ⟨negative σ a b, negative_mem σ unrelated, negative_map σ f a b⟩
  · rintro ⟨p, member, rfl⟩
    rcases member with ⟨s, a, b, related, rfl⟩ | ⟨s, a, b, unrelated, rfl⟩
    · rw [positive_map]
      exact positive_mem (σ ≫ f) related
    · rw [negative_map]
      exact negative_mem (σ ≫ f) unrelated

/-- An ambient collision cannot erase the original negative clause. -/
theorem collision_rejects {T : Theory} {B : EQ.Signature} (σ : T.sig ⟶ B)
    {s : T.sig.S} {a b : Ground T.sig s}
    (unrelated : ¬ Rel T (closedContext T.sig) a b)
    (collision : a.map σ = b.map σ) (N : NativeModel B) :
    ¬ Satisfies N (spectrum T σ) := by
  intro h
  apply unrelated
  apply ((satisfies_iff_exactGroundKernel σ N).mp h s a b).mp
  unfold evaluate
  exact (EQ.Term.eval_map σ (Γ := closedContext T.sig) (decode N)
    (fun i => i.elim0) a).symm.trans
      ((congrArg (fun t => t.eval (decode N) (fun i => i.elim0)) collision).trans
        (EQ.Term.eval_map σ (Γ := closedContext T.sig) (decode N)
          (fun i => i.elim0) b))

end Silmaril.Logic.Algebraic.Initial.Matching.SignedSpectrum
