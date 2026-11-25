module

public import Silmaril.Courses.Cambridge.L3.Denotation
public import Silmaril.Courses.Cambridge.ReturnSpecification.Institution

/-! # Denotational truth for the L3 finite may-return institution -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.DenotationalInstitution

open Denotation
open ReturnSpecification (Claim)
open Silmaril.Semantics.Operational

/-- A denotational observation retains both the value expression and the store. -/
def observesReturn (source target : Config) : Prop :=
  ∃ v : Value, v.val = target.expr ∧ Returns (denote source.expr) source.store v target.store

theorem observesReturn_iff (source target : Config) (admitted : Fragment source.expr) :
    observesReturn source target ↔
      OperationalInstitution.semantics.May source (.returned target) := by
  rw [OperationalInstitution.may_return_iff]
  rcases source with ⟨e, s⟩
  rcases target with ⟨e', s'⟩
  constructor
  · rintro ⟨⟨v, ready⟩, rfl, returned⟩
    exact ⟨sound admitted returned, ready⟩
  · rintro ⟨trace, ready⟩
    exact ⟨⟨e', ready⟩, rfl, complete admitted trace⟩

def Admitted : Claim Config → Prop
  | .mayReturn source | .mayReturnTo source _ => Fragment source.expr

def Denotes : Claim Config → Prop
  | .mayReturn source => ∃ target, observesReturn source target
  | .mayReturnTo source target => observesReturn source target

theorem observed_iff (claim : Claim Config) (admitted : Admitted claim) :
    claim.observed (ReturnSpecification.semantics .l3) ↔ Denotes claim := by
  cases claim with
  | mayReturn source =>
      exact exists_congr (fun target => (observesReturn_iff source target admitted).symm)
  | mayReturnTo source target => exact (observesReturn_iff source target admitted).symm

/-- The existing catalogue institution admits denotational evaluation of
every conjunct whose source is in the compositional fragment. -/
theorem holds_iff {slots : Nat} (catalogue : StepSpecification.Catalogue ⟨.l3, slots⟩)
    (sentence : ReturnSpecification.Sentence ⟨.l3, slots⟩)
    (admitted : ∀ claim ∈ sentence, Admitted (claim.map catalogue)) :
    ReturnSpecification.Holds ⟨.l3, slots⟩ catalogue sentence ↔
      ∀ claim ∈ sentence, Denotes (claim.map catalogue) := by
  rw [ReturnSpecification.holds_iff]
  exact forall₂_congr fun claim mem =>
    ((claim.map catalogue).observed_iff .l3).symm.trans
      (observed_iff (claim.map catalogue) (admitted claim mem))

theorem observed_data_iff {T : Ty} (shape : DataType T) (source : Config)
    (admitted : Fragment source.expr) (result : shape.Result) (store : Store) :
    (Claim.mayReturnTo source ⟨(shape.value result).val, store⟩).observed
        (ReturnSpecification.semantics .l3) ↔
      shape.Observes source.expr source.store result store := by
  change OperationalInstitution.semantics.May source (.returned _) ↔ _
  rw [OperationalInstitution.may_return_iff, adequate_data admitted]
  exact and_iff_left (shape.value result).property

end Silmaril.Courses.Cambridge.L3.DenotationalInstitution
