module

public import Silmaril.Logic.Kore.Operational.Text.Defs
public import Silmaril.Logic.Kore.Operational.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Text

/-- A checked program retains its actual parsed declarations and validated alias. -/
theorem check_source {input : String} {p : CheckedProgram} (h : check input = some p) :
    ∃ parsed, parse input = some parsed ∧
      parsed.aliasDeclaration.elaborate = some (p.context, p.aliasDefinition) ∧
      parsed.declarations = p.declarations ∧
      checkInput p.context p.aliasDefinition p.declarations = some p.checked := by
  cases hp : parse input with
  | none => simp [check, hp] at h
  | some parsed =>
    cases ha : parsed.aliasDeclaration.elaborate with
    | none => simp [check, hp, ha] at h
    | some pair =>
      rcases pair with ⟨Γ, a⟩
      cases hc : checkInput Γ a parsed.declarations with
      | none => simp [check, hp, ha, hc] at h
      | some checked =>
        simp [check, hp, ha, hc] at h
        subst p
        exact ⟨parsed, rfl, ha, rfl, hc⟩

/-- An installed rule comes from an actual axiom declaration, and every accepted
an axiom declaration installs its rule. Claims contribute no transition. -/
theorem checkInput_axioms_iff (Γ : Context) (a : Alias) {ds : List Declaration}
    {checked : CheckedInput} (h : checkInput Γ a ds = some checked) (r : Rule) :
    r ∈ checked.axioms ↔ ∃ d ∈ ds, transitionRule Γ a d = some r := by
  induction ds generalizing checked with
  | nil =>
    simp [checkInput] at h
    subst checked
    simp
  | cons d ds ih =>
    cases he : elaborateRule Γ a d with
    | none => simp [checkInput, he] at h
    | some first =>
      cases hc : checkInput Γ a ds with
      | none => simp [checkInput, he, hc] at h
      | some rest =>
        cases hk : d.kind <;> simp [checkInput, he, hc, hk] at h <;>
          subst checked <;> simp [transitionRule, hk, he, ih hc, List.mem_cons, eq_comm]

/-- The matching result is tied to an axiom found in the checked source text. -/
theorem declaration_matching_sound {input : String} {p : CheckedProgram}
    (h : check input = some p) (d : Declaration) (hd : d ∈ p.declarations)
    (r : Rule) (hr : transitionRule p.context p.aliasDefinition d = some r) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step p.checked.axioms))
      (Reachability.encode KSort.config r.compile) := by
  obtain ⟨_, _, _, _, hc⟩ := check_source h
  exact compiled_matching_sound _ r ((checkInput_axioms_iff _ _ hc r).2 ⟨d, hd, hr⟩)

end Silmaril.Logic.Kore.Operational.Text
