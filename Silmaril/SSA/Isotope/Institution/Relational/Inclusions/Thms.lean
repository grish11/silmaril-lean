module

public import Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Relational.Inclusions

public section

namespace Silmaril.Isotope.Institution.Relational

open CategoryTheory Semantics Silmaril.Logic.Institution

universe u v w q

section Evaluation

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

/-- The native SeqCase embedding preserves the outcome predicate at the given derivation. -/
theorem seqCase_denoteRelation (M : RelationModel D Φ)
    {t : Silmaril.Isotope.LetSeq.LocallyNameless.Tm ν Φ n}
    (d : Silmaril.Isotope.LetSeq.LocallyNameless.Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A) :
    (Morphism.SeqCase.derivation d).denoteRelation D M γ ρ b ↔
      d.denoteRelation D M γ ρ b :=
  seqCase_denoteRelation_proof M d γ ρ b

/-- The native CaseIter embedding preserves the outcome predicate at the given derivation. -/
theorem caseIter_denoteRelation (M : RelationModel D Φ)
    {t : Silmaril.Isotope.LetCase.LocallyNameless.Tm ν Φ n}
    (d : Silmaril.Isotope.LetCase.LocallyNameless.Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A) :
    (Morphism.CaseIter.derivation d).denoteRelation D M γ ρ b ↔
      d.denoteRelation D M γ ρ b :=
  caseIter_denoteRelation_proof M d γ ρ b

/-- The composite embedding preserves the outcome predicate at the selected derivation. -/
theorem seqIter_denoteRelation (M : RelationModel D Φ)
    {t : Silmaril.Isotope.LetSeq.LocallyNameless.Tm ν Φ n}
    (d : Silmaril.Isotope.LetSeq.LocallyNameless.Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A) :
    (Morphism.CaseIter.derivation (Morphism.SeqCase.derivation d)).denoteRelation D M γ ρ b ↔
      d.denoteRelation D M γ ρ b :=
  (caseIter_denoteRelation M (Morphism.SeqCase.derivation d) γ ρ b).trans
    (seqCase_denoteRelation M d γ ρ b)

end Evaluation

variable {τ ε ν : Type u} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q : InstrSig τ ε}

/-- Both original endpoint witnesses are mapped by the native inclusion. -/
theorem seqCaseSentence_eq (e : LetSeq.Sentence P Γ) :
    seqCaseSentence e =
      ⟨e.1, ⟨Morphism.SeqCase.embed e.2.1.1, Morphism.SeqCase.derivation e.2.1.2⟩,
        ⟨Morphism.SeqCase.embed e.2.2.1, Morphism.SeqCase.derivation e.2.2.2⟩⟩ :=
  Silmaril.Isotope.Institution.seqCase_sen Γ P e

/-- Inclusion commutes with opcode relabelling on the whole sentence with its witnesses. -/
theorem seqCaseSentence_natural (g : P ⟶ Q) (e : LetSeq.Sentence P Γ) :
    seqCaseSentence (LetSeq.Sentence.translate g e) =
      LetCase.Sentence.translate g (seqCaseSentence e) := by
  have h := congrArg Corridor.sen ((Silmaril.Isotope.Institution.seqCaseRho Γ).naturality g)
  exact congrFun h e

/-- Both original endpoint witnesses are mapped by the native inclusion. -/
theorem caseIterSentence_eq (e : LetCase.Sentence P Γ) :
    caseIterSentence e =
      ⟨e.1, ⟨Morphism.CaseIter.embed e.2.1.1, Morphism.CaseIter.derivation e.2.1.2⟩,
        ⟨Morphism.CaseIter.embed e.2.2.1, Morphism.CaseIter.derivation e.2.2.2⟩⟩ :=
  Silmaril.Isotope.Institution.caseIter_sen Γ P e

/-- Inclusion commutes with opcode relabelling on the whole sentence with its witnesses. -/
theorem caseIterSentence_natural (g : P ⟶ Q) (e : LetCase.Sentence P Γ) :
    caseIterSentence (LetCase.Sentence.translate g e) =
      LetIter.Sentence.translate g (caseIterSentence e) := by
  have h := congrArg Corridor.sen ((Silmaril.Isotope.Institution.caseIterRho Γ).naturality g)
  exact congrFun h e

/-- The composite sentence embedding also commutes with opcode relabelling. -/
theorem seqIterSentence_natural (g : P ⟶ Q) (e : LetSeq.Sentence P Γ) :
    caseIterSentence (seqCaseSentence (LetSeq.Sentence.translate g e)) =
      LetIter.Sentence.translate g (caseIterSentence (seqCaseSentence e)) := by
  rw [seqCaseSentence_natural, caseIterSentence_natural]

variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

/-- Inclusion preserves satisfaction using the same primitive relation and value structure. -/
theorem seqCase_satisfaction (M : Model D P) (e : LetSeq.Sentence P Γ) :
    LetCase.Sentence.Satisfies M (seqCaseSentence e) ↔ LetSeq.Sentence.Satisfies M e := by
  rw [seqCaseSentence_eq]
  exact forall_congr' fun γ => forall_congr' fun ρ => forall_congr' fun b =>
    iff_congr (seqCase_denoteRelation M e.2.1.2 γ ρ b) (seqCase_denoteRelation M e.2.2.2 γ ρ b)

/-- Inclusion preserves satisfaction using the same primitive relation and value structure. -/
theorem caseIter_satisfaction (M : Model D P) (e : LetCase.Sentence P Γ) :
    LetIter.Sentence.Satisfies M (caseIterSentence e) ↔ LetCase.Sentence.Satisfies M e := by
  rw [caseIterSentence_eq]
  exact forall_congr' fun γ => forall_congr' fun ρ => forall_congr' fun b =>
    iff_congr (caseIter_denoteRelation M e.2.1.2 γ ρ b) (caseIter_denoteRelation M e.2.2.2 γ ρ b)

variable (D Γ)

/-- The native LetSeq inclusion as a transformation of relational rooms. -/
@[expose] def seqCaseRho : LetSeq.institution (ε := ε) D Γ ⟶ LetCase.institution (ε := ε) D Γ where
  app P := ⟨seqCaseSentence, 𝟭 (Model D P), seqCase_satisfaction⟩
  naturality _ _ g := Room.hom_ext (funext (seqCaseSentence_natural g)) rfl

/-- The backwards model component commutes with opcode reduct on objects and arrows. -/
theorem seqCase_model_reduct (g : P ⟶ Q) :
    ((seqCaseRho Γ D).app Q).mod ⋙ Model.reductFunctor D g =
      Model.reductFunctor D g ⋙ ((seqCaseRho Γ D).app P).mod := rfl

/-- The inclusion over the identity functor of instruction signatures. -/
@[expose] def seqCaseCoHom : Inst.CoHom (seqInst (ε := ε) Γ D) (caseInst (ε := ε) Γ D) :=
  ⟨𝟭 _, seqCaseRho Γ D ≫ (Functor.leftUnitor _).inv⟩

/-- The native LetCase inclusion as a transformation of relational rooms. -/
@[expose] def caseIterRho : LetCase.institution (ε := ε) D Γ ⟶ LetIter.institution (ε := ε) D Γ where
  app P := ⟨caseIterSentence, 𝟭 (Model D P), caseIter_satisfaction⟩
  naturality _ _ g := Room.hom_ext (funext (caseIterSentence_natural g)) rfl

/-- The backwards model component commutes with opcode reduct on objects and arrows. -/
theorem caseIter_model_reduct (g : P ⟶ Q) :
    ((caseIterRho Γ D).app Q).mod ⋙ Model.reductFunctor D g =
      Model.reductFunctor D g ⋙ ((caseIterRho Γ D).app P).mod := rfl

/-- The inclusion over the identity functor of instruction signatures. -/
@[expose] def caseIterCoHom : Inst.CoHom (caseInst (ε := ε) Γ D) (iterInst (ε := ε) Γ D) :=
  ⟨𝟭 _, caseIterRho Γ D ≫ (Functor.leftUnitor _).inv⟩

/-- The composite native inclusion from LetSeq to LetIter. -/
@[expose] def seqIterCoHom : Inst.CoHom (seqInst (ε := ε) Γ D) (iterInst (ε := ε) Γ D) :=
  (seqCaseCoHom Γ D).comp (caseIterCoHom Γ D)

variable {D Γ}

theorem seqIter_satisfaction (M : Model D P) (e : LetSeq.Sentence P Γ) :
    LetIter.Sentence.Satisfies M (caseIterSentence (seqCaseSentence e)) ↔
      LetSeq.Sentence.Satisfies M e :=
  (caseIter_satisfaction M (seqCaseSentence e)).trans (seqCase_satisfaction M e)

end Silmaril.Isotope.Institution.Relational
