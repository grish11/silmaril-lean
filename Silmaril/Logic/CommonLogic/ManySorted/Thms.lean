module

public import Silmaril.Logic.CommonLogic.ManySorted.Defs
import Silmaril.Proofs.Logic.CommonLogic.ManySorted

@[expose] public section

namespace Silmaril.Logic.CommonLogic.ManySorted

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic

/-- A typed decoder model is precisely a CL model of the operation typing theory. -/
theorem wellTyped_iff {S : FOL.Signature} (M : Core.Model (signature S)) :
    WellTyped M ↔ ∀ p ∈ typingTheory S, p.Holds M Fin.elim0 Fin.elim0 :=
  Silmaril.Proofs.Logic.CommonLogic.ManySorted.wellTyped_iff M

theorem term_map {S T : FOL.Signature} (f : S ⟶ T) {n k : Nat} {Γ : Fin n → S.S}
    {s : S.S} (t : EQ.Term S.toSignature Γ s) :
    (term (k := k) t).map (signatureMap f) = term (t.map f.toHom) :=
  Silmaril.Proofs.Logic.CommonLogic.ManySorted.term_map f t

theorem formula_map {S T : FOL.Signature} (f : S ⟶ T) {n k : Nat} {Γ : Fin n → S.S}
    (p : FOL.Formula S Γ) :
    (formula (k := k) p).map (signatureMap f) = formula (p.map f) :=
  Silmaril.Proofs.Logic.CommonLogic.ManySorted.formula_map f p

theorem term_eval {S : FOL.Signature} {n k : Nat} {Γ : Fin n → S.S} {s : S.S}
    (M : TypedModel S) (ρ : ∀ i, (decode M).carrier (Γ i))
    (σ : Fin k → List M.obj.Discourse) (t : EQ.Term S.toSignature Γ s) :
    (term t).eval M.obj (fun i => (ρ i).val) σ = (t.eval (decode M).toAlgebra ρ).val :=
  Silmaril.Proofs.Logic.CommonLogic.ManySorted.term_eval M ρ σ t

/-- No nonempty assumption is made on any decoded carrier. -/
theorem formula_holds {S : FOL.Signature} {n k : Nat} {Γ : Fin n → S.S}
    (M : TypedModel S) (p : FOL.Formula S Γ) (ρ : ∀ i, (decode M).carrier (Γ i))
    (σ : Fin k → List M.obj.Discourse) :
    p.Holds (decode M) ρ ↔ (formula p).Holds M.obj (fun i => (ρ i).val) σ :=
  Silmaril.Proofs.Logic.CommonLogic.ManySorted.formula_holds M p ρ σ

theorem sentence_map {S T : FOL.Signature} (f : S ⟶ T) (p : FOL.Sentence S) :
    (sentence p).map (signatureMap f) = sentence (p.map f) := formula_map f p.formula

theorem sentence_holds {S : FOL.Signature} (M : TypedModel S) (p : FOL.Sentence S) :
    p.Holds (decode M) ↔ (sentence p).Holds M.obj Fin.elim0 Fin.elim0 := by
  have hρ : (fun i : Fin 0 =>
      ((Fin.elim0 i : (decode M).carrier (p.ctx i))).val) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  have hh := formula_holds M p.formula (fun i => i.elim0) Fin.elim0
  rw [hρ] at hh
  exact hh

/-- Model decoding commutes with reduct on objects and on all retained arrows. -/
theorem models_natural {S T : FOL.Signature} (f : S ⟶ T) :
    typedReduct f ⋙ models S = models T ⋙ FOL.Structure.reduct f := rfl

end Silmaril.Logic.CommonLogic.ManySorted
