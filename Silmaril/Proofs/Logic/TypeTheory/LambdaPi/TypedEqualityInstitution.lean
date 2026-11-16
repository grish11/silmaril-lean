module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution.Defs

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityInstitution

open Silmaril.Logic.TypeTheory
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Institution
open CategoryTheory Silmaril.Logic.Institution

theorem satisfaction {S T : Signature} (F : Map S T) (M : Model T) (q : Sentence S) :
    M.Satisfies (F.sentence q) ↔ (Model.mk M.target (Map.comp F M.assignment)).Satisfies q := by
  simp only [Model.Satisfies, Map.sentence, Map.comp, IntensionalMLTT.Term.subst_comp]

theorem sound {S : Signature} (q : Sentence S)
    (h : Equality S.context S.context q.left q.right q.carrier) (M : Model S) :
    M.Satisfies q :=
  h.subst (.signature M.target.formed) M.assignment.terms M.assignment.typed

theorem complete {S : Signature} (q : Sentence S)
    (h : ∀ M : Model S, M.Satisfies q) :
    Equality S.context S.context q.left q.right q.carrier := by
  simpa only [Model.Satisfies, Map.identity, IntensionalMLTT.Term.subst_var] using
    h ⟨S, Map.identity S⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityInstitution
