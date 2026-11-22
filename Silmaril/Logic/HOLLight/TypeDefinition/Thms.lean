module

public import Silmaril.Logic.HOLLight.TypeDefinition.Defs
import Silmaril.Proofs.Logic.HOLLight.TypeDefinition.Basic

@[expose] public section

namespace Silmaril.Logic.HOLLight.TypeDefinition

universe u

theorem abs_rep {A : Carrier.{u}} {P : A → Carrier.bool.{u}}
    {inhabited : ∃ value, Carrier.Truth (P value)} (value : PredicateCarrier P inhabited) :
    abs P inhabited (rep value) = value := Silmaril.Proofs.Logic.HOLLight.TypeDefinition.abs_rep value

theorem rep_abs_iff {A : Carrier.{u}} {P : A → Carrier.bool.{u}}
    (inhabited : ∃ value, Carrier.Truth (P value)) (value : A) :
    rep (abs P inhabited value) = value ↔ Carrier.Truth (P value) :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.rep_abs_iff inhabited value

namespace TruthExample

theorem signature_valid : signature.Valid :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.TruthExample.signature_valid

theorem preserves_initial_types (ρ : TypeValuation.{u}) (A : Ty)
    (wellFormed : A.WellFormed initialSignature.tyOps) :
    A.denote typeModel ρ = A.denote TypeModel.standard ρ :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.TruthExample.preserves_initial_types ρ A wellFormed

theorem witness_derived (sig : Signature) : Derives sig [] ∅ witnessExists :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.TruthExample.witness_derived sig

theorem witness_exists : Valid model.{u} witnessExists :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.TruthExample.witness_exists

theorem abstract_represent : Valid model.{u} abstractRepresent :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.TruthExample.abstract_represent

theorem represent_abstract : Valid model.{u} representAbstract :=
  Silmaril.Proofs.Logic.HOLLight.TypeDefinition.TruthExample.represent_abstract

end TruthExample
end Silmaril.Logic.HOLLight.TypeDefinition
