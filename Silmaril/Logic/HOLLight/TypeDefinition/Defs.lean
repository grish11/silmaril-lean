module

public import Silmaril.Logic.HOLLight.Semantics.Validity

@[expose] public section

/-! # Inhabited predicates in HOL Light models

This is a semantic construction. The current kernel has no type-definition
inference rule. In particular this file adds no object-theory axiom.
-/

namespace Silmaril.Logic.HOLLight.TypeDefinition

universe u

abbrev PredicateCarrier {A : Carrier.{u}} (P : A → Carrier.bool.{u})
    (inhabited : ∃ value, Carrier.Truth (P value)) : Carrier.{u} :=
  ⟨{value : A // Carrier.Truth (P value)}, ⟨⟨inhabited.choose, inhabited.choose_spec⟩⟩⟩

def rep {A : Carrier.{u}} {P : A → Carrier.bool.{u}}
    {inhabited : ∃ value, Carrier.Truth (P value)} : PredicateCarrier P inhabited → A :=
  Subtype.val

/-- Abstraction off the predicate is total, but its result there is unspecified. -/
noncomputable def abs {A : Carrier.{u}} (P : A → Carrier.bool.{u})
    (inhabited : ∃ value, Carrier.Truth (P value)) (value : A) : PredicateCarrier P inhabited :=
  @dite _ (Carrier.Truth (P value)) (Classical.propDecidable _)
    (fun accepted => ⟨value, accepted⟩) (fun _ => ⟨inhabited.choose, inhabited.choose_spec⟩)

namespace TruthExample

noncomputable def predicate (value : Carrier.bool.{u}) : Carrier.bool.{u} :=
  Carrier.eq Carrier.bool value Carrier.truth

theorem inhabited : ∃ value, Carrier.Truth (predicate.{u} value) :=
  ⟨Carrier.truth, (Carrier.truth_eq _ _).mpr rfl⟩

def definedType : Ty := .app 0 []
def absScheme : Scheme := ⟨0, .arr .bool definedType⟩
def repScheme : Scheme := ⟨0, .arr definedType .bool⟩
def signature : Signature := ⟨[0], [absScheme, repScheme]⟩

noncomputable def typeModel : TypeModel.{u} :=
  ⟨fun symbol args => match symbol, args with
    | 0, [] => PredicateCarrier predicate inhabited
    | _, _ => Carrier.unit⟩

noncomputable def model : Model.{u} signature where
  toTypeModel := typeModel
  constant name scheme lookup _ := by
    match name with
    | 0 =>
        have same : absScheme = scheme := Option.some.inj lookup
        subst scheme
        exact abs predicate inhabited
    | 1 =>
        have same : repScheme = scheme := Option.some.inj lookup
        subst scheme
        exact rep (inhabited := inhabited)
    | name + 2 => simp [signature] at lookup

def abstractTerm : Tm := .const (.user 0 [])
def representTerm : Tm := .const (.user 1 [])
def predicateTerm : Tm := .lam .bool (Tm.equal .bool (.bvar 0) Tm.truth)

def witnessExists : Tm := Tm.ex .bool predicateTerm

def abstractRepresent : Tm := Tm.all definedType (.lam definedType
  (Tm.equal definedType (.app abstractTerm (.app representTerm (.bvar 0))) (.bvar 0)))

/-- Equality of Booleans expresses equivalence with membership in the predicate. -/
def representAbstract : Tm := Tm.all .bool (.lam .bool
  (Tm.equal .bool (Tm.equal .bool (.app representTerm (.app abstractTerm (.bvar 0))) (.bvar 0))
    (.app predicateTerm (.bvar 0))))

end TruthExample
end Silmaril.Logic.HOLLight.TypeDefinition
