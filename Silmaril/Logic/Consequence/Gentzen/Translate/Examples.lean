module

public import Silmaril.Logic.Consequence.Gentzen.Translate.Thms

/-!
# Examples: translations and signed lifts

* Lifting the pure identity calculus on atoms to signed literals gives explosion `p, ¬p ⊢` and
  excluded middle `⊢ p, ¬p` (`identity_lift_explosion`, `identity_lift_excluded_middle`): the
  atoms of a negative literal change sides, where the identity axiom `p ⊢ p` applies.
* Its positive part is the identity calculus again (`identity_lift_posPart`).
* Renaming atoms along `f` carries the identity calculus into itself as a core `Translation`
  (`identityRename`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Translate.Examples

/-- The pure identity calculus on atoms `ℕ`. -/
abbrev identity : Seq ℕ := Derives defaultRules ⊥

theorem identity_p_p : identity [0] [0] :=
  .refl trivial (List.mem_singleton_self 0) (List.mem_singleton_self 0)

theorem identity_lift_explosion : signedLift identity [.pos 0, .neg 0] [] := by
  simpa [signedLift, posAtoms, negAtoms] using identity_p_p

theorem identity_lift_excluded_middle : signedLift identity [] [.pos 0, .neg 0] := by
  simpa [signedLift, posAtoms, negAtoms] using identity_p_p

theorem identity_lift_posPart : MultiSystem.posPart (signedLift identity) = identity :=
  posPart_signedLift identity

/-- Renaming atoms translates the identity calculus into itself. -/
def identityRename (f : ℕ → ℕ) : Translation identity identity :=
  ofMapDerives (Rules.Hom.default f) (fun _ _ h => h.elim)

end Silmaril.Consequence.Gentzen.Translate.Examples
