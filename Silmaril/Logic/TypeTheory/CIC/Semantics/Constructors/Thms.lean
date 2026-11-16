module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Defs
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.ConstructorTelescopes

@[expose] public section

/-! # Realization of actual dependent constructor declarations

Small dependent tuples construct actual tagged ZFSet domains and curried
constructor traces. Interpretation of actual oldest-first source telescopes
reconstructs the full local field context, and evaluates source product/lambda
abstraction and actual argument application. Explicit constructor assignments
then inhabit their actual interpreted declaration types.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.ConstructorTelescopeLaws
  (evaluates_extendedSubst extendedList_eq_reverse_extendedSubst evaluates_extendedList
   telescope_trace_mem mem_constructorLayer constructor_trace_mem interpretsTelescope_length
   interpretsTelescope_unique interpretsTelescope_context evaluates_telescope_products evaluates_telescope_lambdas evaluates_telescope_application
   constructorLayer_constructor_rule constructorLayer_application)

universe u

/-- Actual source constructor lookup/typing and its local semantic declaration obligation give realization together. -/
theorem constructorLayer_constructor_source_and_value {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {sig : GlobalContext} {Γ : Context}
    {reference : InductiveRef} {ui : List Universe} {block : MutualInductiveBody} {body : InductiveBody}
    {constructor : ConstructorBody} {count : ℕ} (telescopes : Fin count → ValueTelescope.{u}) (index : Fin count)
    (hΓ : CoreWfLocal sig Γ)
    (hsource : sig.environment.lookupConstructor reference index.val = some (block, body, constructor))
    (hinstance : sig.ValidInstance block.universes ui)
    (hlookup : globals.constructor reference index.val ui =
      some ((telescopes index).trace (fun xs => constructorValue index.val ((telescopes index).arguments xs))))
    (htype : Evaluates ρ universes globals values (constructorType reference ui block constructor)
      ((telescopes index).pi (fun _ => constructorLayer count telescopes []))) :
    CoreTyping sig Γ (.constructor reference index.val ui) (constructorType reference ui block constructor) ∧
      HasValueAt ρ universes globals values (.constructor reference index.val ui) (constructorType reference ui block constructor) :=
  ⟨CoreTyping.constructor hΓ hsource hinstance, constructorLayer_constructor_rule telescopes index hlookup htype⟩

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
