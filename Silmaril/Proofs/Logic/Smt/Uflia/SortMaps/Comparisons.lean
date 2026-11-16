module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps
open CategoryTheory Silmaril.Inst Silmaril.Logic.Algebraic Silmaril.Logic.Institution

theorem fixedSort_operation {U : Type} {A B : Uflia.Signature U} (f : A ⟶ B)
    {n inputs output} (op : Operation A n inputs output) :
    Hom.operation ((fixedSortSignatures U).map f) op = Operation.map f op := by
  cases op <;> rfl

theorem fixedSort_term {U : Type} {A B : Uflia.Signature U} (f : A ⟶ B)
    {k : Nat} {Γ : Fin k → SortCode U} {s : SortCode U}
    (p : ManySorted.Term A.expanded Γ s) :
    Hom.term ((fixedSortSignatures U).map f) p =
      ManySorted.Term.map (Uflia.Signature.expandMap f) p := by
  induction p with
  | var i => rfl
  | app op args ih =>
      simp only [Hom.term, ManySorted.Term.map, fixedSort_operation]
      exact congrArg (ManySorted.Term.app (Operation.map f op)) (funext ih)

theorem fixedSort_formula {U : Type} {A B : Uflia.Signature U} (f : A ⟶ B)
    (p : Formula A) :
    Hom.formula ((fixedSortSignatures U).map f) p = Term.map f p :=
  eq_of_heq ((Hom.formula_heq ((fixedSortSignatures U).map f) p).trans (heq_of_eq (fixedSort_term f p)))

theorem fixedSort_reductFunctor {U : Type} {A B : Uflia.Signature U} (f : A ⟶ B) :
    Hom.reductFunctor ((fixedSortSignatures U).map f) = Model.reductFunctor f := rfl

noncomputable def fixedSortComparison (U : Type) :
    Inst.CoHom (HomModels.inst U) inst where
  Φ := fixedSortSignatures U
  ρ :=
    { app A := ⟨id, 𝟭 _, fun _ _ => Iff.rfl⟩
      naturality := by
        intro A B f
        apply Room.hom_ext
        · exact (funext (fixedSort_formula f)).symm
        · exact (fixedSort_reductFunctor f).symm }

theorem fixedSortComparison_modelExpansive {U : Type} (A : Uflia.Signature U) :
    ((fixedSortComparison U).ρ.app A).ModelExpansive := fun M => ⟨M, rfl⟩

theorem fixedSort_quantifiedTerm {U : Type} {A B : Uflia.Signature U} (f : A ⟶ B)
    {k : Nat} {Γ : Fin k → SortCode U} {s : SortCode U}
    (p : Quantified.Term A Γ s) :
    Hom.quantifiedTerm ((fixedSortSignatures U).map f) p = p.map f := by
  induction p with
  | var i => rfl
  | app op args ih =>
      simp only [Hom.quantifiedTerm, Quantified.Term.map, fixedSort_operation]
      exact congrArg (Quantified.Term.app (Operation.map f op)) (funext ih)
  | all s body ih => exact congrArg (Quantified.Term.all s) ih
  | ex s body ih => exact congrArg (Quantified.Term.ex s) ih

theorem fixedSort_quantifiedSentence {U : Type} {A B : Uflia.Signature U} (f : A ⟶ B)
    (p : Quantified.Sentence A) :
    Hom.quantifiedSentence ((fixedSortSignatures U).map f) p = p.map f := by
  exact fixedSort_quantifiedTerm f p

noncomputable def fixedSortQuantifiedComparison (U : Type) :
    Inst.CoHom (Quantified.HomModels.inst U) QuantifiedModels.inst where
  Φ := fixedSortSignatures U
  ρ :=
    { app A := ⟨id, 𝟭 _, fun _ _ => Iff.rfl⟩
      naturality := by
        intro A B f
        apply Room.hom_ext
        · exact (funext (fixedSort_quantifiedSentence f)).symm
        · exact (fixedSort_reductFunctor f).symm }

theorem fixedSortQuantifiedComparison_modelExpansive {U : Type} (A : Uflia.Signature U) :
    ((fixedSortQuantifiedComparison U).ρ.app A).ModelExpansive := fun M => ⟨M, rfl⟩

end Silmaril.Logic.Smt.Uflia.SortMaps
