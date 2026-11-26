module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Native.Defs

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe v₁ v₂ u₁ u₂ u v w

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem denote_embed_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (d : LetIter.LocallyNameless.Derivation Φ Γ β t A) :
    denote J P M (derivation d) = LetIter.Semantics.Categorical.denote J M d := by
  induction d <;> simp only [derivation, denote, LetIter.Semantics.Categorical.denote, *]

section ProofRelevant

open LetIter.ProofRelevant.Semantics.Categorical renaming
  TypeModel → RelevantModel, InstructionModel → RelevantInstructions, denote → relevantDenote,
  ctxObj → relevantCtx, boundObj → relevantBound, envObj → relevantEnv,
  ctxLookup → relevantCtxLookup, boundLookup → relevantBoundLookup,
  freeLookup → relevantFree, boundVar → relevantVar, envSnocIso → relevantSnoc,
  envPairHom → relevantPair

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem exactObj_eq [Subtyping τ] (N : RelevantModel τ V) (A : τ) :
    (exactTypeModel N).obj A = N.obj A := rfl

omit [DecidableEq ν] [SymmetricCategory V] [DistributiveTensor V] in
private theorem exactCtx_eq [Subtyping τ] (N : RelevantModel τ V) (Γ : Ctx ν τ) :
    LetIter.Semantics.Categorical.ctxObj (exactTypeModel N) Γ = relevantCtx N Γ := by
  induction Γ <;> simp only [LetIter.Semantics.Categorical.ctxObj, relevantCtx, *]; rfl

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem exactBound_eq [Subtyping τ] (N : RelevantModel τ V) {n : Nat} (β : BoundCtx τ n) :
    LetIter.Semantics.Categorical.boundObj (exactTypeModel N) β = relevantBound N β := by
  induction β <;> simp only [LetIter.Semantics.Categorical.boundObj, relevantBound, *]; rfl

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
private theorem pre_fst_heq {R S A B : V} (h : R = S) {f : R ⟶ B} {g : S ⟶ B}
    (hg : HEq f g) : HEq (fst R A ≫ f) (fst S A ≫ g) := by
  cases h
  cases hg
  rfl

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
private theorem snd_heq {R S A : V} (h : R = S) : HEq (snd R A) (snd S A) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem exactCtx_lookup [Subtyping τ] (N : RelevantModel τ V) {Γ : Ctx ν τ}
    (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    HEq (LetIter.Semantics.Categorical.ctxLookup (exactTypeModel N) x h) (relevantCtxLookup N x h) := by
  induction Γ generalizing A with
  | nil => simp [Ctx.lookup] at h
  | snoc Γ nm B ih =>
    cases nm with
    | none =>
      simp only [LetIter.Semantics.Categorical.ctxLookup, relevantCtxLookup]
      exact pre_fst_heq (A := N.obj B) (exactCtx_eq N Γ) (ih (by simpa [Ctx.lookup] using h))
    | some y =>
      by_cases hxy : x = y
      · subst y
        have hBA : B = A := by simpa [Ctx.lookup] using h
        subst A
        simp only [LetIter.Semantics.Categorical.ctxLookup, relevantCtxLookup]
        simp only [dite_true]
        exact snd_heq (A := N.obj B) (exactCtx_eq N Γ)
      · simp only [LetIter.Semantics.Categorical.ctxLookup, relevantCtxLookup, dite_eq_right hxy]
        exact pre_fst_heq (A := N.obj B) (exactCtx_eq N Γ) (ih (by simpa [Ctx.lookup, hxy] using h))

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem exactBound_lookup [Subtyping τ] (N : RelevantModel τ V) {n : Nat} {β : BoundCtx τ n}
    (i : Fin n) :
    HEq (LetIter.Semantics.Categorical.boundLookup (exactTypeModel N) (β := β) i)
      (relevantBoundLookup N (β := β) i) := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact snd_heq (A := N.obj A) (exactBound_eq N β)
    · exact pre_fst_heq (A := N.obj A) (exactBound_eq N β) (ih j)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem denote_embed_nativeTyping_proof [Subtyping τ] (N : RelevantModel τ V)
    [RelevantInstructions J N Φ] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (d : LetIter.LocallyNameless.Derivation Φ Γ β t A) :
    letI := exactInstructionModel J N (Φ := Φ)
    HEq (denote J P (exactTypeModel N) (derivation d)) (relevantDenote J N (nativeTyping d)) := by
  rw [denote_embed_proof]
  induction d <;> simp only [nativeTyping, relevantDenote, LetIter.Semantics.Categorical.denote,
    LetIter.ProofRelevant.Semantics.Categorical.abort, LetIter.Semantics.Categorical.freeLookup,
    relevantFree, LetIter.Semantics.Categorical.boundVar, relevantVar,
    LetIter.Semantics.Categorical.envSnocIso, relevantSnoc,
    LetIter.Semantics.Categorical.envPairHom, relevantPair] <;>
    congr! (partialApp := false) 8 <;>
    first
    | exact exactCtx_eq N _
    | exact exactBound_eq N _
    | exact exactCtx_lookup N _ _
    | exact exactBound_lookup N _
    | simp only [LetIter.Semantics.Categorical.envObj, relevantEnv, exactCtx_eq, exactBound_eq, exactObj_eq]

end ProofRelevant

end Silmaril.Isotope.LetParIter.Categorical
