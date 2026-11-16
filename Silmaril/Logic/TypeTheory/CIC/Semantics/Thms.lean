module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Defs
public import Silmaril.Logic.TypeTheory.CIC.Typing.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.SetSemantics

@[expose] public section

/-! # Concrete trace semantics attached to CIC syntax and local contexts

Trace beta and dependent Pi/Prop laws are proved for actual ZFSet values.
The finite `UniverseSets count` hierarchy records local closure laws.
The `Semantics.Universes` layer constructs supplies from finite Grothendieck
towers, without a global soundness field. The Coherence
extension discharges application substitution coherence. Tagged cases without
constructor-local definitions are interpreted by the Cases extension. General
checked inductive denotations and guarded fix/cofix remain open. Primitive
projection evaluation is supplied by the kernel and its Projections extension.
No full CIC soundness, consistency or semantic institution is claimed.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

export Silmaril.Proofs.Logic.TypeTheory.CIC.SetSemanticsLaws
  (mem_traceLambda mem_traceApply trace_beta mem_tracePi tracePi_intro tracePi_elim traceLambda_empty
   mem_truth truth_subset truth_in_propositionUniverse tracePi_truth tracePi_propositionUniverse
   sort_super sort_cumul sort_product local_length sort_rule product_rule lambda_rule
   product_prop_rule product_sprop_rule application_fibre application_rule evaluates_beta constant_rule
   identity_has_value identity_applied_local traceLambda_empty_domain traceApply_empty off_domain_beta_counterexample)

/-- The closed proposition identity has both an actual core typing derivation and a concrete set denotation. -/
theorem identity_source_and_value (sig : GlobalContext) (ρ : LevelName → ℕ)
    (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    CoreTyping sig [] propositionIdentity propositionIdentityType ∧
      HasValueAt ρ universes globals [] propositionIdentity propositionIdentityType :=
  ⟨CoreTyping.propIdentity sig CoreWfLocal.nil, identity_has_value ρ universes globals⟩

/-- Its application to a local proposition is typed by CIC and realized in a genuine local set environment. -/
theorem identity_application_source_and_value (sig : GlobalContext) (ρ : LevelName → ℕ)
    (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) (P : Value.{u}) (hP : P ∈ propositionUniverse) :
    CoreTyping sig [{ binder := {}, type := .sort .prop }] (.app propositionIdentity (.rel 0)) (.sort .prop) ∧
    InterpretsLocal ρ universes globals [{ binder := {}, type := .sort .prop }] [P] ∧
      HasValueAt ρ universes globals [P] (.app propositionIdentity (.rel 0)) (.sort .prop) :=
  ⟨CoreTyping.propIdentityApplication sig CoreWfLocal.nil, identity_applied_local ρ universes globals P hP⟩

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
