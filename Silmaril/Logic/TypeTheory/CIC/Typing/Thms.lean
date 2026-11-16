module

public import Silmaril.Logic.TypeTheory.CIC.Typing.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.Typing

@[expose] public section

/-! # Nonvacuous examples of the declarative typing fragment -/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Identity on propositions is typable in every checked local context. -/
theorem CoreTyping.propIdentity (sig : GlobalContext) {Γ : Context} (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig Γ (.lam {} (.sort .prop) (.rel 0)) (.prod {} (.sort .prop) (.sort .prop)) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.TypingLaws.propIdentity sig hΓ

/-- Its product type inhabits the join of the two domain/range super-sort universes. -/
theorem CoreTyping.propIdentityType (sig : GlobalContext) {Γ : Context}
    (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig Γ (.prod {} (.sort .prop) (.sort .prop))
      (.sort (.type (.max (.succ .zero) (.succ .zero)))) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.TypingLaws.propIdentityType sig hΓ

/-- The application to a local proposition is typed using the actual application rule. -/
theorem CoreTyping.propIdentityApplication (sig : GlobalContext) {Γ : Context}
    (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig ({ binder := {}, type := .sort .prop } :: Γ)
      (.app (.lam {} (.sort .prop) (.rel 0)) (.rel 0)) (.sort .prop) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.TypingLaws.propIdentityApplication sig hΓ

end Silmaril.Logic.TypeTheory.CIC
