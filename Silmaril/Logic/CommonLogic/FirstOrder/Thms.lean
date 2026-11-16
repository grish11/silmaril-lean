module

public import Silmaril.Logic.CommonLogic.FirstOrder.Defs
import Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder

@[expose] public section

namespace Silmaril.Logic.CommonLogic.FirstOrder

open Silmaril.Logic.CommonLogic
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

theorem term_map {S T : Signature} (f : S ⟶ T) {n k : Nat} {Γ : Fin n → Unit}
    {s : Unit} (t : EQ.Term (publicSignature S).toSignature Γ s) :
    (term (k := k) t).map (clMap f) = term (t.map (publicMap f).toHom) :=
  Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder.term_map f t

theorem formula_map {S T : Signature} (f : S ⟶ T) {n k : Nat} {Γ : Fin n → Unit}
    (p : FOL.Formula (publicSignature S) Γ) :
    (formula (k := k) p).map (clMap f) = formula (p.map (publicMap f)) :=
  Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder.formula_map f p

theorem term_eval {S : Signature} {n k : Nat} {Γ : Fin n → Unit} {s : Unit}
    (M : Core.Model (clSignature S)) (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse)
    (t : EQ.Term (publicSignature S).toSignature Γ s) :
    (term t).eval M ρ σ = t.eval (decode M).toAlgebra ρ :=
  Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder.term_eval M ρ σ t

theorem formula_holds {S : Signature} {n k : Nat} {Γ : Fin n → Unit}
    (M : Core.Model (clSignature S)) (p : FOL.Formula (publicSignature S) Γ)
    (ρ : Fin n → M.Discourse) (σ : Fin k → List M.Discourse) :
    p.Holds (decode M) ρ ↔ (formula p).Holds M ρ σ :=
  Silmaril.Proofs.Logic.CommonLogic.IndependentFirstOrder.formula_holds M p ρ σ

theorem sentence_map {S T : Signature} (f : S ⟶ T) (p : FOL.Sentence (publicSignature S)) :
    (sentence p).map (clMap f) = sentence (p.map (publicMap f)) := formula_map f p.formula

theorem sentence_holds {S : Signature} (M : Core.Model (clSignature S))
    (p : FOL.Sentence (publicSignature S)) :
    p.Holds (decode M) ↔ (Core.room (clSignature S)).Sat M (sentence p) :=
  formula_holds M p.formula Fin.elim0 Fin.elim0

/-- The model comparison commutes on objects and on every actual model homomorphism. -/
theorem models_natural {S T : Signature} (f : S ⟶ T) :
    Core.Model.reduct (clMap f) ⋙ models S = models T ⋙ FOL.Structure.reduct (publicMap f) := rfl

def corridor (S : Signature) : institution.obj S ⟶ Core.institution.obj (signatures.obj S) :=
  ⟨sentence, models S, fun M p => (sentence_holds M p).symm⟩

/-- A genuine institution comorphism from single-sorted public FOL to the full admitted CL core. -/
def comorphism : Inst.CoHom inst Core.inst where
  Φ := signatures
  ρ :=
    { app := corridor
      naturality := fun {_ _} f => Room.hom_ext (funext fun p => (sentence_map f p).symm)
        (models_natural f).symm }

theorem nonemptyModels_natural {S T : Signature} (f : S ⟶ T) :
    Core.Model.reduct (clMap f) ⋙ nonemptyModels S = nonemptyModels T ⋙ nonemptyReduct f := rfl

def nonemptyComparison (S : Signature) : nonemptyRoom S ⟶ Core.room (clSignature S) :=
  ⟨sentence, nonemptyModels S, fun M p => (sentence_holds M p).symm⟩

/-- The same syntax and decoder, with the source restricted to its nonempty full model categories. -/
def nonemptyComorphism : Inst.CoHom nonemptyInst Core.inst where
  Φ := signatures
  ρ :=
    { app := nonemptyComparison
      naturality := fun {_ _} f => Room.hom_ext (funext fun p => (sentence_map f p).symm)
        (nonemptyModels_natural f).symm }

end Silmaril.Logic.CommonLogic.FirstOrder
