module

public import Silmaril.Logic.TypeTheory.CIC.Typing.Defs
public import Silmaril.Logic.TypeTheory.CIC.Syntax.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.TypingLaws

open Silmaril.Logic.TypeTheory.CIC

private theorem prop_sort (sig : GlobalContext) {Γ : Context} (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig Γ (.sort .prop) (.sort (.type (.succ .zero))) :=
  .sort hΓ trivial

private theorem prop_context (sig : GlobalContext) {Γ : Context} (hΓ : CoreWfLocal sig Γ) :
    CoreWfLocal sig ({ binder := {}, type := .sort .prop } :: Γ) :=
  .assumption hΓ (prop_sort sig hΓ) rfl

theorem propIdentity (sig : GlobalContext) {Γ : Context} (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig Γ (.lam {} (.sort .prop) (.rel 0)) (.prod {} (.sort .prop) (.sort .prop)) := by
  apply CoreTyping.lambda (na := {}) (prop_sort sig hΓ) rfl
  simpa only [Term.lift] using CoreTyping.rel (n := 0) (prop_context sig hΓ) rfl

theorem propIdentityType (sig : GlobalContext) {Γ : Context} (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig Γ (.prod {} (.sort .prop) (.sort .prop))
      (.sort (.type (.max (.succ .zero) (.succ .zero)))) :=
  CoreTyping.product (na := {}) (prop_sort sig hΓ) rfl (prop_sort sig (prop_context sig hΓ))

theorem propIdentityApplication (sig : GlobalContext) {Γ : Context} (hΓ : CoreWfLocal sig Γ) :
    CoreTyping sig ({ binder := {}, type := .sort .prop } :: Γ)
      (.app (.lam {} (.sort .prop) (.rel 0)) (.rel 0)) (.sort .prop) := by
  have hp : CoreWfLocal sig ({ binder := {}, type := .sort .prop } :: Γ) := prop_context sig hΓ
  have ha : CoreTyping sig ({ binder := {}, type := .sort .prop } :: Γ) (.rel 0) (.sort .prop) := by
    simpa only [Term.lift] using CoreTyping.rel (n := 0) hp rfl
  simpa only [Term.subst] using
    CoreTyping.app (propIdentityType sig hp) (propIdentity sig hp) ha

end Silmaril.Proofs.Logic.TypeTheory.CIC.TypingLaws
