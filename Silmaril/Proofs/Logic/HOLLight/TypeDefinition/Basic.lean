module

public import Silmaril.Logic.HOLLight.TypeDefinition.Defs
import Silmaril.Logic.HOLLight.Classical

@[expose] public section

namespace Silmaril.Proofs.Logic.HOLLight.TypeDefinition

open Silmaril.Logic.HOLLight
open Silmaril.Logic.HOLLight.TypeDefinition

universe u

theorem abs_rep {A : Carrier.{u}} {P : A → Carrier.bool.{u}}
    {inhabited : ∃ value, Carrier.Truth (P value)} (value : PredicateCarrier P inhabited) :
    abs P inhabited (rep value) = value := by
  apply Subtype.ext
  exact congrArg Subtype.val (dite_eq_left value.property)

theorem rep_abs_iff {A : Carrier.{u}} {P : A → Carrier.bool.{u}}
    (inhabited : ∃ value, Carrier.Truth (P value)) (value : A) :
    rep (abs P inhabited value) = value ↔ Carrier.Truth (P value) := by
  constructor
  · intro same
    exact same ▸ (abs P inhabited value).property
  · intro accepts
    exact congrArg Subtype.val (dite_eq_left accepts)

namespace TruthExample

open Silmaril.Logic.HOLLight.TypeDefinition.TruthExample

theorem signature_valid : signature.Valid := by
  intro scheme member
  rcases List.mem_cons.mp member with rfl | rest
  · exact ⟨⟨trivial, rfl, trivial⟩, trivial, trivial⟩
  · have same : scheme = repScheme := List.mem_singleton.mp rest
    subst scheme
    exact ⟨⟨⟨rfl, trivial⟩, trivial⟩, trivial, trivial⟩

theorem preserves_initial_types (ρ : TypeValuation.{u}) (A : Ty)
    (wellFormed : A.WellFormed initialSignature.tyOps) :
    A.denote typeModel ρ = A.denote TypeModel.standard ρ := by
  induction A using Ty.induction_on with
  | var _ | bool | ind => rfl
  | arr A B domain codomain => exact congrArg₂ Carrier.arr (domain wellFormed.1) (codomain wellFormed.2)
  | app symbol args _ => simp [initialSignature, Ty.WellFormed] at wellFormed

theorem witness_derived (sig : Signature) : Derives sig [] ∅ witnessExists := by
  have bodyTyping : HasType sig [.bool] (Tm.equal .bool (.bvar 0) Tm.truth) .bool :=
    .equal trivial (.bvar rfl trivial) .truth
  have predicateTyping : HasType sig [] predicateTerm (.arr .bool .bool) :=
    .lam trivial bodyTyping
  apply Derives.exIntro (A := .bool) trivial predicateTyping (x := Tm.truth) HasType.truth
  have beta := Derives.generalBeta (theory := []) bodyTyping
    (HasType.truth (sig := sig) (Γ := []))
  exact beta.symm.eqMpSame (.refl HasType.truth)

variable {ρ : TypeValuation.{u}} {ν : FreeEnv model ρ}
  {Γ : List Ty} {η : BoundEnv model ρ Γ}

private theorem evalAbs : Eval model ρ ν η abstractTerm (.arr .bool definedType)
    (abs predicate inhabited) :=
  .const η (.user (s := absScheme) rfl (signature_valid.lookup (c := 0) rfl) rfl (by simp))

private theorem evalRep : Eval model ρ ν η representTerm (.arr definedType .bool)
    (rep (P := predicate) (inhabited := inhabited)) :=
  .const η (.user (s := repScheme) rfl (signature_valid.lookup (c := 1) rfl) rfl (by simp))

private theorem evalPredicate : Eval model ρ ν η predicateTerm (.arr .bool .bool) predicate :=
  .lam (A := .bool) trivial (fun value => Eval.equal (.bvar (η.extend value) rfl trivial) Eval.truth)

theorem witness_exists : Valid model.{u} witnessExists := by
  intro _ _
  exact ⟨_, Eval.ex trivial evalPredicate, (Carrier.truth_ex _ _).mpr inhabited⟩

theorem abstract_represent : Valid model.{u} abstractRepresent := by
  intro ρ ν
  have wellFormed : definedType.WellFormed signature.tyOps := ⟨rfl, trivial⟩
  have evaluation : Eval model ρ ν BoundEnv.empty abstractRepresent .bool
      (Carrier.all (PredicateCarrier predicate inhabited) (fun value =>
        Carrier.eq (PredicateCarrier predicate inhabited) (abs predicate inhabited (rep value)) value)) :=
    Eval.all wellFormed (.lam wellFormed (fun value =>
      let variableEval := Eval.bvar (BoundEnv.extend value BoundEnv.empty) rfl wellFormed
      Eval.equal (.app evalAbs (.app evalRep variableEval)) variableEval))
  exact ⟨_, evaluation, (Carrier.truth_all _ _).mpr (fun value => (Carrier.truth_eq _ _).mpr (abs_rep value))⟩

theorem represent_abstract : Valid model.{u} representAbstract := by
  intro ρ ν
  have evaluation : Eval model ρ ν BoundEnv.empty representAbstract .bool
      (Carrier.all Carrier.bool (fun value => Carrier.eq Carrier.bool
        (Carrier.eq Carrier.bool (rep (abs predicate inhabited value)) value) (predicate value))) :=
    Eval.all (A := .bool) trivial (.lam (A := .bool) trivial (fun value =>
      let variableEval := Eval.bvar (A := .bool) (BoundEnv.extend value BoundEnv.empty) rfl trivial
      Eval.equal (Eval.equal (.app evalRep (.app evalAbs variableEval)) variableEval)
        (.app evalPredicate variableEval)))
  refine ⟨_, evaluation, (Carrier.truth_all _ _).mpr (fun value => (Carrier.truth_eq _ _).mpr ?_)⟩
  exact Carrier.bool_ext ((Carrier.truth_eq _ _).trans (rep_abs_iff inhabited value))

end TruthExample
end Silmaril.Proofs.Logic.HOLLight.TypeDefinition
