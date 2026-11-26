module

public import Silmaril.SSA.Isotope.LetParCase.Thms
public import Silmaril.SSA.Isotope.LetParIter.Thms
public import Silmaril.SSA.Isotope.Parallel.Hierarchy.Defs
public import Silmaril.Raw.SSA.Isotope.Morphism.Models
import Silmaril.Proofs.SSA.Isotope.Parallel.Hierarchy

/-! # Commuting inclusions of the native and parallel let calculi -/

@[expose] public section

namespace Silmaril.Isotope.Parallel.Hierarchy

universe u v w q r

variable {ν : Type v} {Φ : Type w} {n m : Nat}

/-- Both paths include a LetSeq term as the same parallel case term. -/
theorem seqCase_commutes (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    LetParCase.embed (Morphism.SeqCase.embed t) = LetParCase.ofLetPar (LetPar.embed t) :=
  LetParCase.embed_seqCase t

/-- Both paths include a LetCase term as the same parallel iteration term. -/
theorem caseIter_commutes (t : LetCase.LocallyNameless.Tm ν Φ n) :
    LetParIter.embed (Morphism.CaseIter.embed t) = LetParIter.ofLetParCase (LetParCase.embed t) :=
  LetParIter.embed_caseIter t

/-- The outer rectangle commutes from LetSeq to LetParIter. -/
theorem seqIter_commutes (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed t)) =
      LetParIter.ofLetParCase (LetParCase.ofLetPar (LetPar.embed t)) := by
  rw [caseIter_commutes, seqCase_commutes]

/-- The composite embedding commutes with renaming under every binder. -/
theorem seqIter_rename (ρ : Fin n → Fin m) (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed (t.rename ρ))) =
      (LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed t))).rename ρ := by
  rw [Morphism.SeqCase.embed_rename, Morphism.CaseIter.embed_rename, LetParIter.embed_rename]

/-- The composite embedding commutes with simultaneous bound substitution. -/
theorem seqIter_bsubst (σ : Fin n → LetSeq.LocallyNameless.Tm ν Φ m)
    (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed (t.bsubst σ))) =
      (LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed t))).bsubst
        (fun i => LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed (σ i)))) := by
  simp only [Morphism.SeqCase.embed_bsubst, Morphism.CaseIter.embed_bsubst, LetParIter.embed_bsubst]

section Quotients

/-- The induced map of classes is injective exactly when the term map reflects equations. -/
theorem quotientMap_injective_iff {α β : Type*} {source : Setoid α} {target : Setoid β}
    (embed : α → β) (preserves : ∀ a b, source.r a b → target.r (embed a) (embed b)) :
    Function.Injective (Quotient.map' embed preserves) ↔
      ∀ a b, target.r (embed a) (embed b) → source.r a b :=
  ⟨fun injective _ _ h => Quotient.exact (injective (Quotient.sound h)),
    fun reflects a b => Quotient.inductionOn₂ a b fun x y h =>
      Quotient.sound (reflects x y (Quotient.exact h))⟩

/-- Target models whose restrictions separate source classes suffice for reflection. -/
theorem quotientMap_injective_of_separating_reducts {α β : Type*}
    {source : Setoid α} {target : Setoid β} {Model : Type*} {Observation : Model → Type*}
    (embed : α → β) (preserves : ∀ a b, source.r a b → target.r (embed a) (embed b))
    (interpret : (M : Model) → β → Observation M)
    (sound : ∀ M a b, target.r a b → interpret M a = interpret M b)
    (separates : ∀ a b, ¬ source.r a b → ∃ M, interpret M (embed a) ≠ interpret M (embed b)) :
    Function.Injective (Quotient.map' embed preserves) :=
  (quotientMap_injective_iff embed preserves).2 fun a b h =>
    Classical.byContradiction fun distinct =>
      let ⟨M, separatesInM⟩ := separates a b distinct
      separatesInM (sound M _ _ h)

open Theory

variable {ν : Type v} {Φ : Type w} {τ : Type u} {ε : Type r}
  [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ] [HasEff Φ ε]
  {Γ : Ctx ν τ} {i : TypingIndex τ}

/-- Raw parallel terms with exact typing in a fixed context and result type. -/
abbrev TypedTerm (tier : Tier) [CaseTypes tier τ] (Φ : Type w) [HasTy Φ τ]
    (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  {t : Tm tier ν Φ i.depth // HasType Φ Γ i.bound t i.result}

/-- The setoid packages the existing typed congruence at one typing index. -/
def typedTermSetoid {tier : Tier} [CaseTypes tier τ] (pureEff : ε)
    (extra : EqScheme tier ν Φ) (Γ : Ctx ν τ) (i : TypingIndex τ) :
    Setoid (TypedTerm tier Φ Γ i) where
  r a b := Equiv pureEff extra Γ i.bound a.val b.val i.result
  iseqv := ⟨fun a => .refl a.property, Equiv.symm, Equiv.trans⟩

/-- Include an exactly typed LetSeq term in LetPar. -/
def seqParTerm : LetSeq.LocallyNameless.TypedTerm Φ Γ i → TypedTerm .seq Φ Γ i :=
  Subtype.map LetPar.embed (fun _ => LetPar.embed_hasType)

/-- Include an exactly typed LetCase term in LetParCase. -/
def caseParTerm : LetCase.LocallyNameless.TypedTerm Φ Γ i → TypedTerm .case Φ Γ i :=
  Subtype.map LetParCase.embed (fun _ => LetParCase.embed_hasType)

/-- Include an exactly typed LetIter term in LetParIter. -/
def iterParTerm : LetIter.LocallyNameless.TypedTerm Φ Γ i → TypedTerm .iter Φ Γ i :=
  Subtype.map LetParIter.embed (fun _ ht =>
    (LetIter.LocallyNameless.Derivation.ofHasType ht).map LetParIter.derivation)

/-- Add case forms to an exactly typed parallel term. -/
def parCaseTerm : TypedTerm .seq Φ Γ i → TypedTerm .case Φ Γ i :=
  Subtype.map LetParCase.ofLetPar (fun _ => LetParCase.ofLetPar_hasType)

/-- Add feedback forms to an exactly typed parallel case term. -/
def parCaseIterTerm : TypedTerm .case Φ Γ i → TypedTerm .iter Φ Γ i :=
  Subtype.map LetParIter.ofLetParCase (fun _ ht => ht.map LetParIter.ofLetParCaseDerivation)

theorem seqCaseTerm_injective :
    Function.Injective (@(Morphism.SeqCase.typedTranslation (Φ := Φ) Γ).term i) := by
  intro a b h
  exact Subtype.ext (Morphism.SeqCase.embed_injective (congrArg Subtype.val h))

theorem caseIterTerm_injective :
    Function.Injective (@(Morphism.CaseIter.typedTranslation (Φ := Φ) Γ).term i) := by
  intro a b h
  exact Subtype.ext (Morphism.CaseIter.embed_injective (congrArg Subtype.val h))

theorem seqParTerm_injective : Function.Injective (seqParTerm : _ → TypedTerm .seq Φ Γ i) :=
  Subtype.map_injective _ LetPar.embed_injective

theorem caseParTerm_injective : Function.Injective (caseParTerm : _ → TypedTerm .case Φ Γ i) :=
  Subtype.map_injective _ LetParCase.embed_injective

theorem parCaseTerm_injective : Function.Injective (parCaseTerm : _ → TypedTerm .case Φ Γ i) :=
  Subtype.map_injective _ LetParCase.ofLetPar_injective

theorem iterParTerm_injective : Function.Injective (iterParTerm : _ → TypedTerm .iter Φ Γ i) :=
  Subtype.map_injective _ LetParIter.embed_injective

theorem parCaseIterTerm_injective :
    Function.Injective (parCaseIterTerm : _ → TypedTerm .iter Φ Γ i) :=
  Subtype.map_injective _ (Tm.widen_injective Tier.caseIter)

/-- The composite parallel inclusion is also injective before taking any quotient. -/
theorem seqIterTerm_injective :
    Function.Injective (parCaseIterTerm ∘ parCaseTerm ∘ seqParTerm :
      LetSeq.LocallyNameless.TypedTerm Φ Γ i → TypedTerm .iter Φ Γ i) :=
  parCaseIterTerm_injective.comp (parCaseTerm_injective.comp seqParTerm_injective)

/-- The lower square commutes in each exact typing fiber. -/
theorem seqCaseTerm_commutes (t : LetSeq.LocallyNameless.TypedTerm Φ Γ i) :
    caseParTerm ((Morphism.SeqCase.typedTranslation Γ).term t) = parCaseTerm (seqParTerm t) :=
  Subtype.ext (seqCase_commutes t.val)

/-- The upper square commutes in each exact typing fiber. -/
theorem caseIterTerm_commutes (t : LetCase.LocallyNameless.TypedTerm Φ Γ i) :
    iterParTerm ((Morphism.CaseIter.typedTranslation Γ).term t) = parCaseIterTerm (caseParTerm t) :=
  Subtype.ext (caseIter_commutes t.val)

/-- The composite comparing typed LetSeq and typed LetParIter. -/
theorem seqIterTerm_commutes (t : LetSeq.LocallyNameless.TypedTerm Φ Γ i) :
    iterParTerm ((Morphism.CaseIter.typedTranslation Γ).term ((Morphism.SeqCase.typedTranslation Γ).term t)) =
      parCaseIterTerm (parCaseTerm (seqParTerm t)) :=
  Subtype.ext (seqIter_commutes t.val)

/-- The horizontal quotient map along the native LetSeq inclusion. -/
def seqCaseQuot (pureEff : ε) : LetSeq.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i →
    LetCase.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i :=
  Quotient.map' (Morphism.SeqCase.typedTranslation Γ).term (fun _ _ eq => Morphism.SeqCase.embed_equiv eq)

/-- The horizontal quotient map along the native LetCase inclusion. -/
def caseIterQuot (pureEff : ε) : LetCase.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i →
    LetIter.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i :=
  Quotient.map' (Morphism.CaseIter.typedTranslation Γ).term (fun _ _ eq => Morphism.CaseIter.embed_equiv eq)

/-- The map on LetSeq classes induced by the parallel inclusion. -/
def seqParQuot (pureEff : ε) : LetSeq.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i →
    Quotient (typedTermSetoid (tier := .seq) (Φ := Φ) pureEff (fun _ _ => False) Γ i) :=
  Quotient.map' seqParTerm (fun _ _ eq => LetPar.embed_equiv eq)

/-- The map on LetCase classes induced by the parallel inclusion. -/
def caseParQuot (pureEff : ε) : LetCase.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i →
    Quotient (typedTermSetoid (tier := .case) pureEff (CaseRule (Φ := Φ) pureEff) Γ i) :=
  Quotient.map' caseParTerm (fun _ _ eq => LetParCase.embed_equiv eq)

/-- The map on LetPar classes induced by adding case forms. -/
def parCaseQuot (pureEff : ε) :
    Quotient (typedTermSetoid (tier := .seq) (Φ := Φ) pureEff (fun _ _ => False) Γ i) →
    Quotient (typedTermSetoid (tier := .case) pureEff (CaseRule (Φ := Φ) pureEff) Γ i) :=
  Quotient.map' parCaseTerm (fun _ _ eq => LetParCase.ofLetPar_equiv eq)

/-- The lower square descends to exact typed equivalence classes. -/
theorem seqCaseQuot_commutes (pureEff : ε)
    (q : LetSeq.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i) :
    caseParQuot pureEff (seqCaseQuot pureEff q) = parCaseQuot pureEff (seqParQuot pureEff q) :=
  Quotient.inductionOn q (fun t => congrArg (Quotient.mk _) (seqCaseTerm_commutes t))

section IterationQuotients

variable [Subtyping τ]

/-- The upper theory retains a derivation at each endpoint. -/
abbrev IterationTerm (Φ : Type w) [HasTy Φ τ] (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  (t : LetParIter.Tm ν Φ i.depth) × Derivation Φ Γ i.bound t i.result

/-- The actual LetParIter congruence on exact derivations. -/
def iterParSetoid (pureEff : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :
    Setoid (IterationTerm Φ Γ i) where
  r a b := LetParIter.Equiv pureEff Γ a.2 b.2
  iseqv := ⟨fun a => .refl a.2, LetParIter.Equiv.symm, LetParIter.Equiv.trans⟩

/-- Native proof-relevant equations restricted to the exact, coercion-free endpoints. -/
def nativeIterSetoid (pureEff : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :
    Setoid (LetIter.LocallyNameless.Models.Carrier Φ Γ i) where
  r a b := LetIter.ProofRelevant.LocallyNameless.TypedEquiv.Related pureEff Γ
    (LetParIter.nativeTyping a.2) (LetParIter.nativeTyping b.2)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨h⟩ => ⟨.symm h⟩,
    fun ⟨h⟩ ⟨k⟩ => ⟨.trans h k⟩⟩

/-- The vertical quotient map at the proof-relevant native endpoints. -/
def iterParDerivationQuot (pureEff : ε) : Quotient (nativeIterSetoid (Φ := Φ) pureEff Γ i) →
    Quotient (iterParSetoid (Φ := Φ) pureEff Γ i) :=
  Quotient.map' (fun a => ⟨LetParIter.embed a.1, LetParIter.derivation a.2⟩)
    (fun a b h => LetParIter.Equiv.native a.2 b.2 h)

/-- Choose one upper derivation per exact typed raw term. -/
noncomputable def chooseIterationTerm (t : TypedTerm .iter Φ Γ i) : IterationTerm Φ Γ i :=
  ⟨t.val, Classical.choice t.property⟩

/-- Compatibility required to send the two raw term quotients into the
derivation quotient at the chosen upper typings. -/
structure IterationQuotientCompatibility (pureEff : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) : Prop where
  native (a b : LetIter.LocallyNameless.TypedTerm Φ Γ i) :
    LetIter.LocallyNameless.Equiv pureEff Γ i.bound a.val b.val i.result →
      LetParIter.Equiv pureEff Γ (chooseIterationTerm (iterParTerm a)).2 (chooseIterationTerm (iterParTerm b)).2
  parallel (a b : TypedTerm .case Φ Γ i) :
    LetParCase.Equiv pureEff Γ i.bound a.val b.val i.result →
      LetParIter.Equiv pureEff Γ (chooseIterationTerm (parCaseIterTerm a)).2
        (chooseIterationTerm (parCaseIterTerm b)).2

/-- The raw native quotient descends given compatibility with the upper typing choices. -/
noncomputable def iterParQuot (pureEff : ε) (h : IterationQuotientCompatibility (Φ := Φ) pureEff Γ i) :
    LetIter.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i →
    Quotient (iterParSetoid (Φ := Φ) pureEff Γ i) :=
  Quotient.map' (chooseIterationTerm ∘ iterParTerm) h.native

/-- The parallel case quotient descends given compatibility with the upper typing choices. -/
noncomputable def parCaseIterQuot (pureEff : ε) (h : IterationQuotientCompatibility (Φ := Φ) pureEff Γ i) :
    Quotient (typedTermSetoid (tier := .case) pureEff (CaseRule (Φ := Φ) pureEff) Γ i) →
    Quotient (iterParSetoid (Φ := Φ) pureEff Γ i) :=
  Quotient.map' (chooseIterationTerm ∘ parCaseIterTerm) h.parallel

/-- Under compatibility, the upper square descends to the stated quotients. -/
theorem caseIterQuot_commutes (pureEff : ε) (h : IterationQuotientCompatibility (Φ := Φ) pureEff Γ i)
    (q : LetCase.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i) :
    iterParQuot pureEff h (caseIterQuot pureEff q) = parCaseIterQuot pureEff h (caseParQuot pureEff q) :=
  Quotient.inductionOn q (fun t => congrArg (Quotient.mk _ ∘ chooseIterationTerm) (caseIterTerm_commutes t))

/-- Under compatibility, the composite square descends to the stated quotients. -/
theorem seqIterQuot_commutes (pureEff : ε) (h : IterationQuotientCompatibility (Φ := Φ) pureEff Γ i)
    (q : LetSeq.LocallyNameless.Models.TermQuotient (Φ := Φ) pureEff Γ i) :
    iterParQuot pureEff h (caseIterQuot pureEff (seqCaseQuot pureEff q)) =
      parCaseIterQuot pureEff h (parCaseQuot pureEff (seqParQuot pureEff q)) := by
  rw [caseIterQuot_commutes, seqCaseQuot_commutes]

end IterationQuotients

end Quotients

section Semantics

open Semantics

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- The lower square preserves the exact derivations as well as their terms. -/
theorem seqCaseDerivation_commutes {t : LetSeq.LocallyNameless.Tm ν Φ n}
    (d : LetSeq.LocallyNameless.Derivation Φ Γ β t A) :
    (⟨_, LetParCase.derivation (Morphism.SeqCase.derivation d)⟩ :
      (a : LetParCase.Tm ν Φ n) × Derivation Φ Γ β a A) =
        ⟨_, LetParCase.ofLetParDerivation (LetPar.derivation d)⟩ :=
  Proofs.seqCase_derivation d

/-- The upper square preserves the exact derivations as well as their terms. -/
theorem caseIterDerivation_commutes {t : LetCase.LocallyNameless.Tm ν Φ n}
    (d : LetCase.LocallyNameless.Derivation Φ Γ β t A) :
    (⟨_, LetParIter.derivation (Morphism.CaseIter.derivation d)⟩ :
      (a : LetParIter.Tm ν Φ n) × Derivation Φ Γ β a A) =
        ⟨_, LetParIter.ofLetParCaseDerivation (LetParCase.derivation d)⟩ :=
  Proofs.caseIter_derivation d

/-- Every parallel case program retains its shared-interpreter denotation in the reduct. -/
theorem denote_case_reduct {D : τ → Type q} [ProductModel D] [UnitModel D]
    {m : Type q → Type q} [Monad m] (M : InstructionModel D Φ m) (P : ParOp m) (C : Control .iter D m)
    {t : LetParCase.Tm ν Φ n} (d : Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (LetParIter.ofLetParCaseDerivation d).denote D M P C γ ρ =
      d.denote D M P (restrictControl C) γ ρ :=
  Proofs.denote_ofLetParCase M P C d γ ρ

/-- Restrict the same parallel case model along either path from LetSeq. -/
theorem seqCase_denote_commutes (D : τ → Type q)
    [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {m : Type q → Type q} [Monad m] (M : InstructionModel D Φ m) (P : ParOp m)
    {t : LetSeq.LocallyNameless.Tm ν Φ n} (d : LetSeq.LocallyNameless.Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (LetParCase.derivation (Morphism.SeqCase.derivation d)).denote D M P (Control.case D m) γ ρ =
      (LetParCase.ofLetParDerivation (LetPar.derivation d)).denote D M P (Control.case D m) γ ρ := by
  simp only [LetParCase.denote_derivation, Morphism.SeqCase.denote_derivation,
    LetParCase.denote_ofLetParDerivation, LetPar.denote_derivation]

end Semantics

section IterationSemantics

open LetIter.ProofRelevant.Semantics

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, q} τ] [DecidableEq ν] [HasTy Φ τ]
  {ε : Type r} [HasEff Φ ε] [Bot ε] {m : Type q → Type q} [Monad m] [Elgot.Iterate m]
  [InstructionModel Φ τ ε m] {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- Both paths through the upper square have the same interpretation in the upper model. -/
theorem caseIter_denote_commutes (P : Elgot.ParallelPairing m)
    {t : LetCase.LocallyNameless.Tm ν Φ n} (d : LetCase.LocallyNameless.Derivation Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    LetParIter.denote (ε := ε) P (LetParIter.derivation (Morphism.CaseIter.derivation d)) γ ρ =
      LetParIter.denote (ε := ε) P (LetParIter.ofLetParCaseDerivation (LetParCase.derivation d)) γ ρ :=
  congrArg (fun a => LetParIter.denote (ε := ε) P a.2 γ ρ) (Proofs.caseIter_derivation d)

/-- Both paths around the outer rectangle have the same interpretation in the upper model. -/
theorem seqIter_denote_commutes (P : Elgot.ParallelPairing m)
    {t : LetSeq.LocallyNameless.Tm ν Φ n} (d : LetSeq.LocallyNameless.Derivation Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    LetParIter.denote (ε := ε) P
        (LetParIter.derivation (Morphism.CaseIter.derivation (Morphism.SeqCase.derivation d))) γ ρ =
      LetParIter.denote (ε := ε) P
        (LetParIter.ofLetParCaseDerivation (LetParCase.ofLetParDerivation (LetPar.derivation d))) γ ρ := by
  rw [caseIter_denote_commutes]
  exact congrArg (fun a => LetParIter.denote (ε := ε) P (LetParIter.ofLetParCaseDerivation a.2) γ ρ)
    (Proofs.seqCase_derivation d)

end IterationSemantics

end Silmaril.Isotope.Parallel.Hierarchy
