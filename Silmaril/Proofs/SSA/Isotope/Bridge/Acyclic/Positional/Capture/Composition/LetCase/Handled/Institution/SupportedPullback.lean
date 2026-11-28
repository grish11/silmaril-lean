module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Reduct.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.FreeContext.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel pullbackTypes pullbackInstructions transportArrow
  RegionWitnessPullback regionWitnessPullback ssaSignatureCorridor)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation mapRanked sat_mapRanked)
open LetIter.Semantics.Categorical (TypeModel InstructionModel TypingCoherent denote boundObj boundLookup boundVar
  envObj envSnocIso envPairHom typingCoherent_empty_of_nil)
open LetIter.LocallyNameless (Derivation)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Δ₀" => (Ctx.nil : Ctx Empty υ)

private theorem boundObj_eq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) :
    boundObj (pullbackTypes g M) β = boundObj M (β.mapTypes g.ty) := by
  induction β with
  | nil => rfl
  | snoc β A ih => exact congrArg (fun X => X ⊗ M.obj (g.ty A)) ih

private theorem envObj_eq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) :
    envObj (pullbackTypes g M) Γ₀ β = envObj M Δ₀ (β.mapTypes g.ty) :=
  congrArg (fun X => (𝟙_ V) ⊗ X) (boundObj_eq g M β)

private theorem boundLookup_heq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    HEq (boundLookup (pullbackTypes g M) (β := β) i) (boundLookup M (β := β.mapTypes g.ty) i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
    have e := boundObj_eq g M β
    refine Fin.cases ?_ (fun k => ?_) i
    · change HEq (CartesianMonoidalCategory.snd (boundObj (pullbackTypes g M) β) (M.obj (g.ty A)))
        (CartesianMonoidalCategory.snd (boundObj M (β.mapTypes g.ty)) (M.obj (g.ty A)))
      congr! (config := .unfoldSameFun)
    · have hk := ih k
      have hA := congrArg M.obj (BoundCtx.get_mapTypes g.ty β k).symm
      change HEq
        (CartesianMonoidalCategory.fst (boundObj (pullbackTypes g M) β) (M.obj (g.ty A)) ≫
          boundLookup (pullbackTypes g M) k)
        (CartesianMonoidalCategory.fst (boundObj M (β.mapTypes g.ty)) (M.obj (g.ty A)) ≫
          boundLookup M k)
      congr! (config := .unfoldSameFun)

private theorem envSnocIso_heq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) (A : τ) :
    HEq (envSnocIso (pullbackTypes g M) Γ₀ β A) (envSnocIso M Δ₀ (β.mapTypes g.ty) (g.ty A)) := by
  unfold envSnocIso
  have e := boundObj_eq g M β
  congr! (config := .unfoldSameFun)

private theorem envPairHom_heq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    HEq (envPairHom (pullbackTypes g M) Γ₀ β A B) (envPairHom M Δ₀ (β.mapTypes g.ty) (g.ty A) (g.ty B)) := by
  unfold envPairHom
  have e := boundObj_eq g M β
  have eΓ := envObj_eq g M β
  have eβ := boundObj_eq g M ((β.snoc A).snoc B)
  have eΓAB := envObj_eq g M ((β.snoc A).snoc B)
  congr! (config := .unfoldSameFun)

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem iso_transport {A B D : V} (h : A = B) (i : B ≅ D) : HEq (eqToIso h ≪≫ i) i := by
  subst B
  simp [Iso.refl_trans]

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem initial_transport {A B D : V} (h : A = B) (i : IsInitial B) :
    HEq ((cast (congrArg IsInitial h.symm) i).to D) (i.to D) := by
  subst B
  rfl

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  (M : TypeModel υ V) (I : InstructionModel J M Q.Instr)

/-- Change the result type of a transported derivation along an equation. -/
private theorem retype {n : Nat} {γ : BoundCtx υ n} {s : LetIter.LocallyNameless.Tm Empty Q.Instr n} {A B : υ}
    (h : A = B) {X : Sort 1} (x : X) (d' : Derivation Q.Instr Δ₀ γ s A)
    (hd : HEq x (letI := I; denote J M d')) :
    ∃ d'' : Derivation Q.Instr Δ₀ γ s B, HEq x (letI := I; denote J M d'') := by
  subst h
  exact ⟨d', hd⟩

/-- Every derivation over the source signature has a derivation of the
translated term over the target signature with the same arrow, read in the
pulled-back interpretation. -/
theorem denote_pullback_proof {n : Nat} {β : BoundCtx τ n} {t : LetIter.LocallyNameless.Tm Empty P.Instr n}
    {A : τ} (d : Derivation P.Instr Γ₀ β t A) :
    ∃ d' : Derivation Q.Instr Δ₀ (β.mapTypes g.ty) (t.mapInstr g.instr) (g.ty A),
      HEq (letI := pullbackInstructions g I; denote J (pullbackTypes g M) d) (letI := I; denote J M d') := by
  induction d with
  | fv h => rename_i x _; exact x.elim
  | @bv n β i =>
    have hβ := boundObj_eq g M β
    have hΓ := envObj_eq g M β
    have hA := congrArg M.obj (BoundCtx.get_mapTypes g.ty β i).symm
    have hk := boundLookup_heq g M β i
    refine retype M I (BoundCtx.get_mapTypes g.ty β i) _
      (.bv (ι := i) : Derivation Q.Instr Δ₀ (β.mapTypes g.ty) (.bv i) _) ?_
    simp only [denote, boundVar]
    congr! (config := .unfoldSameFun)
  | @op n β f a ha ih =>
    obtain ⟨a₀, h₀⟩ := ih
    obtain ⟨a', h0⟩ := retype M I (g.source f).symm _ a₀ h₀
    have hΓ := envObj_eq g M β
    have hA := congrArg M.obj (g.source f).symm
    have hB := congrArg M.obj (g.target f).symm
    have hp : HEq ((pullbackInstructions g I).denote f) (I.denote (g.instr f)) := cast_heq _ _
    refine retype M I (g.target f) _ (.op (f := g.instr f) a') ?_
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @let₁ n β a b A B ha hb iha ihb =>
    obtain ⟨a', h0⟩ := iha
    obtain ⟨b', h1⟩ := ihb
    have hΓ := envObj_eq g M β
    have hΓA := envObj_eq g M (β.snoc A)
    have hi := envSnocIso_heq g M β A
    refine ⟨.let₁ a' b', ?_⟩
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @unit n β =>
    have hΓ := envObj_eq g M β
    have hu := congrArg M.obj (SignatureMap.PreservesProducts.unit (g := g))
    have hi : HEq (pullbackTypes g M).unitIso M.unitIso := iso_transport hu _
    refine retype M I (SignatureMap.PreservesProducts.unit (g := g)).symm _
      (.unit : Derivation Q.Instr Δ₀ (β.mapTypes g.ty) .unit _) ?_
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @pair n β a b A B ha hb iha ihb =>
    obtain ⟨a', h0⟩ := iha
    obtain ⟨b', h1⟩ := ihb
    have hΓ := envObj_eq g M β
    have hp := congrArg M.obj (SignatureMap.PreservesProducts.product (g := g) A B)
    have hi : HEq ((pullbackTypes g M).productIso A B) (M.productIso (g.ty A) (g.ty B)) := iso_transport hp _
    refine retype M I (SignatureMap.PreservesProducts.product (g := g) A B).symm _ (.pair a' b') ?_
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @let₂ n β a c A B D ha hc iha ihc =>
    obtain ⟨a₀, h₀⟩ := iha
    obtain ⟨a', h0⟩ := retype M I (SignatureMap.PreservesProducts.product (g := g) A B) _ a₀ h₀
    obtain ⟨c', h1⟩ := ihc
    have hΓ := envObj_eq g M β
    have hΓAB := envObj_eq g M ((β.snoc A).snoc B)
    have hp := congrArg M.obj (SignatureMap.PreservesProducts.product (g := g) A B)
    have hi : HEq ((pullbackTypes g M).productIso A B) (M.productIso (g.ty A) (g.ty B)) := iso_transport hp _
    have he := envPairHom_heq g M β A B
    refine ⟨.let₂ a' c', ?_⟩
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @inl n β a A B ha ih =>
    obtain ⟨a', h0⟩ := ih
    have hΓ := envObj_eq g M β
    have hc := congrArg M.obj (SignatureMap.PreservesSums.coprod (g := g) A B)
    have hi : HEq ((pullbackTypes g M).coprodIso A B) (M.coprodIso (g.ty A) (g.ty B)) := iso_transport hc _
    refine retype M I (SignatureMap.PreservesSums.coprod (g := g) A B).symm _ (.inl a') ?_
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @inr n β b A B hb ih =>
    obtain ⟨b', h0⟩ := ih
    have hΓ := envObj_eq g M β
    have hc := congrArg M.obj (SignatureMap.PreservesSums.coprod (g := g) A B)
    have hi : HEq ((pullbackTypes g M).coprodIso A B) (M.coprodIso (g.ty A) (g.ty B)) := iso_transport hc _
    refine retype M I (SignatureMap.PreservesSums.coprod (g := g) A B).symm _ (.inr b') ?_
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @case n β e l r A B D he hl hr ihe ihl ihr =>
    obtain ⟨e₀, h₀⟩ := ihe
    obtain ⟨e', h0⟩ := retype M I (SignatureMap.PreservesSums.coprod (g := g) A B) _ e₀ h₀
    obtain ⟨l', h1⟩ := ihl
    obtain ⟨r', h2⟩ := ihr
    have hΓ := envObj_eq g M β
    have hΓA := envObj_eq g M (β.snoc A)
    have hΓB := envObj_eq g M (β.snoc B)
    have hc := congrArg M.obj (SignatureMap.PreservesSums.coprod (g := g) A B)
    have hi : HEq ((pullbackTypes g M).coprodIso A B) (M.coprodIso (g.ty A) (g.ty B)) := iso_transport hc _
    have hs := envSnocIso_heq g M β A
    have ht := envSnocIso_heq g M β B
    refine ⟨.case e' l' r', ?_⟩
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @abort n β a D ha ih =>
    obtain ⟨a₀, h₀⟩ := ih
    obtain ⟨a', h0⟩ := retype M I (SignatureMap.PreservesSums.empty (g := g)) _ a₀ h₀
    have hΓ := envObj_eq g M β
    have he := congrArg M.obj (SignatureMap.PreservesSums.empty (g := g))
    have hi : HEq ((pullbackTypes g M).emptyIsInitial.to (M.obj (g.ty D))) (M.emptyIsInitial.to (M.obj (g.ty D))) :=
      initial_transport he M.emptyIsInitial
    refine ⟨.abort a', ?_⟩
    simp only [denote]
    congr! (config := .unfoldSameFun)
  | @iter n β a b A B ha hb iha ihb =>
    obtain ⟨a', h0⟩ := iha
    obtain ⟨b₀, h₀⟩ := ihb
    obtain ⟨b', h1⟩ := retype M I (SignatureMap.PreservesSums.coprod (g := g) B A) _ b₀ h₀
    have hΓ := envObj_eq g M β
    have hΓA := envObj_eq g M (β.snoc A)
    have hc := congrArg M.obj (SignatureMap.PreservesSums.coprod (g := g) B A)
    have hi : HEq ((pullbackTypes g M).coprodIso B A) (M.coprodIso (g.ty B) (g.ty A)) := iso_transport hc _
    have hs := envSnocIso_heq g M β A
    refine ⟨.iter a' b', ?_⟩
    simp only [denote]
    congr! (config := .unfoldSameFun)

/-- Coherent expression typing transports to the pulled-back
interpretation along a signature map that changes types. -/
theorem typingCoherent_pullback_proof
    (coherent : letI := I; TypingCoherent (ν := Empty) J M Q.Instr) :
    letI := pullbackInstructions g I
    TypingCoherent (ν := Empty) J (pullbackTypes g M) P.Instr := by
  let := pullbackInstructions g I
  have nil : ∀ {n : Nat} {β : BoundCtx τ n} {t : LetIter.LocallyNameless.Tm Empty P.Instr n} {A : τ}
      (d e : Derivation P.Instr Γ₀ β t A), denote J (pullbackTypes g M) d = denote J (pullbackTypes g M) e := by
    intro n β t A d e
    obtain ⟨d', hd⟩ := denote_pullback_proof g M I d
    obtain ⟨e', he⟩ := denote_pullback_proof g M I e
    exact eq_of_heq (hd.trans ((heq_of_eq (coherent d' e')).trans he.symm))
  intro Γ n β t A d e
  exact typingCoherent_empty_of_nil (Φ := P.Instr) J (pullbackTypes g M) nil d e

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  [StrongElgotFreydCategory J] in
/-- A value map for a primitive transports along the two type equations. -/
theorem pure_transport_proof {A A' B B' : υ} (hs : A = A') (ht : B = B')
    (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)) (p : M.obj A ⟶ M.obj B) (same : f = J.map p) :
    ∃ p' : M.obj A' ⟶ M.obj B', transportArrow (J := J) (M := M) hs ht f = J.map p' := by
  subst hs ht
  exact ⟨p, same⟩

variable [FreydCategory.CentralUnit J]

omit [FreydCategory.CentralUnit J] in
/-- The pullback of a supported model along a signature map is supported,
at the effect marker that the map sends to the target marker. -/
theorem supported_pullback_proof {pe : ε} (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    (supported : Supported (g.eff pe) K) : Supported pe (K.pullbackOfWitness g w) where
  typing := typingCoherent_pullback_proof g K.types K.instructions supported.typing
  shared := supported.shared
  pure := fun x pure => by
    obtain ⟨p, same⟩ := supported.pure (g.instr x) ((g.effect x).trans (congrArg g.eff pure))
    exact pure_transport_proof K.types (g.source x) (g.target x) _ p same

theorem sat_pullback_proof (K : CoherentRegionModel J Q) (e : RankedEquation P) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J Q).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk K)) (mapRanked g e) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk (K.pullbackOfWitness g (regionWitnessPullback g K)))) e :=
  Silmaril.Isotope.Institution.Acyclic.Captured.sat_mapRanked (J := J) g (ShrinkHoms.toShrinkHoms (Discrete.mk K)) e

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
