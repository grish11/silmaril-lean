module

public import Silmaril.Logic.CommonLogic.FiniteListFOL.Translation.Defs
import Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation

@[expose] public section
namespace Silmaril.Logic.CommonLogic.FiniteListFOL
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder

theorem term_eval {S : Core.Signature} (M : Model S) {n k m : Nat}
    {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence)
    (ξ : Fin n → D M.obj) (ζ : Fin k → List (D M.obj))
    (η : (i : Fin m) → M.obj.obj.carrier (Γ i))
    (hρ : ∀ i, (ρ i).eval M.obj.obj.toAlgebra η = ξ i)
    (hσ : ∀ i, (σ i).eval M.obj.obj.toAlgebra η = FiniteLists.evaluationEquiv M.obj (ζ i))
    {a : Core.Kind} (t : Core.Expr S n k a) :
    (translateTerm ρ σ t).eval M.obj.obj.toAlgebra η =
      encodeValue M a (t.eval (decode M) ξ ζ) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.term_eval M ρ σ ξ ζ η hρ hσ t

theorem formula_holds {S : Core.Signature} (M : Model S) {n k : Nat}
    (p : Core.Formula S n k) : ∀ {m : Nat} {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence)
    (ξ : Fin n → D M.obj) (ζ : Fin k → List (D M.obj))
    (η : (i : Fin m) → M.obj.obj.carrier (Γ i)),
    (∀ i, (ρ i).eval M.obj.obj.toAlgebra η = ξ i) →
    (∀ i, (σ i).eval M.obj.obj.toAlgebra η = FiniteLists.evaluationEquiv M.obj (ζ i)) →
    ((translateFormula ρ σ p).Holds M.obj.obj η ↔ p.Holds (decode M) ξ ζ) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.formula_holds M p

theorem sentence_holds {S : Core.Signature} (M : Model S) (p : Core.Sentence S) :
    (sentence p).Holds M.obj.obj ↔ p.Holds (decode M) Fin.elim0 Fin.elim0 :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.sentence_holds M p

open CategoryTheory

theorem term_map {S T : Core.Signature} (f : S ⟶ T) {n k m : Nat}
    {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence)
    {a : Core.Kind} (t : Core.Expr S n k a) :
    (translateTerm ρ σ t).map (FiniteLists.publicMap (signatureMap f)).toHom =
      translateTerm
        (fun i => (ρ i).map (FiniteLists.publicMap (signatureMap f)).toHom)
        (fun i => (σ i).map (FiniteLists.publicMap (signatureMap f)).toHom) (t.map f) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.term_map f ρ σ t

theorem formula_map {S T : Core.Signature} (f : S ⟶ T) {n k : Nat}
    (p : Core.Formula S n k) : ∀ {m : Nat} {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence),
    (translateFormula ρ σ p).map (FiniteLists.publicMap (signatureMap f)) =
      translateFormula
        (fun i => (ρ i).map (FiniteLists.publicMap (signatureMap f)).toHom)
        (fun i => (σ i).map (FiniteLists.publicMap (signatureMap f)).toHom) (p.map f) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.formula_map f p

theorem sentence_map {S T : Core.Signature} (f : S ⟶ T) (p : Core.Sentence S) :
    FOL.Sentence.map (FiniteLists.publicMap (signatureMap f)) (sentence p) =
      sentence (p.map f) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.sentence_map f p

open Silmaril.Logic.Institution

/-- Full Core sentences translate forwards; full target FOL model arrows decode backwards. -/
noncomputable def comparison (S : Core.Signature) : Core.room S ⟶ room S :=
  ⟨sentence, models S, fun M p => sentence_holds M p⟩

/-- Comparison of the entire admitted Core with independent many-sorted FOL
whose nil/cons reduct is free on its full discourse carrier. -/
noncomputable def comorphism : Inst.CoHom Core.inst inst where
  Φ := 𝟭 Core.Signature
  ρ :=
    { app := comparison
      naturality := fun {_ _} f =>
        Room.hom_ext (funext fun p => (sentence_map f p).symm)
          (models_natural f).symm }

/-- Exact object surjectivity, witnessed by the native finite-list expansion. -/
theorem comparison_modelExpansive (S : Core.Signature) :
    (comparison S).ModelExpansive :=
  fun M => ⟨expand M, decode_expand M⟩

theorem comorphism_modelExpansive : comorphism.ModelExpansive :=
  comparison_modelExpansive

/-- Full-theory satisfiability is preserved and reflected. Forward witnesses
use exact-object ModelExpansive; target witnesses may be any admitted FOL model. -/
theorem sat_transport {S : Core.Signature} (H : Set (Core.Sentence S)) :
    Core.Sat H ↔ TargetSat (sentence '' H) :=
  Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation.corridor_sat_transport
    (comparison S) (comparison_modelExpansive S) H

theorem unsat_transport {S : Core.Signature} (H : Set (Core.Sentence S)) :
    Core.Unsat H ↔ TargetUnsat (sentence '' H) := not_congr (sat_transport H)

/-- Reuse the institution borrowing theorem for semantic consequence. -/
theorem entails_transport {S : Core.Signature} (H : Set (Core.Sentence S))
    (p : Core.Sentence S) :
    (Core.room S).Entails H p ↔ (room S).Entails (sentence '' H) (sentence p) :=
  comorphism.entails_iff comorphism_modelExpansive S H p

end Silmaril.Logic.CommonLogic.FiniteListFOL
