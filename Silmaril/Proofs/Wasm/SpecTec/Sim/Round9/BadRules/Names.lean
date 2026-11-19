module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.BadN.Thms

/-!
# Round 9, RE: `BadFwdN` from the seven rule names

`badNames_fixed` (`decide +kernel`): every rule of `Step`/`Step_read` passes one of the three
checks or is named in `badNames`. `badFwdN_of_rules`: `BadN.BadFwdN` follows from `RuleFwdNm` at
the seven names.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

set_option maxRecDepth 100000 in
/-- **Every rule of `Step`/`Step_read` passes a check or is one of the seven.** -/
theorem badNames_fixed : (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).all (fun p =>
    !Round8.NxStep.stepRel p.1 || p.2.2.2.2.all fun r => Round8.NxStep.goodRule r ||
      ElseBwd.goodRuleE r || BadN.goodRuleN r || badNames.contains (ruleName r)) = true := by
  decide +kernel

/-- A rule of `Step`/`Step_read` that fails the three checks is named in `badNames`. -/
theorem mem_badNames {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems))
    (hg : Round8.NxStep.goodRule (.ruleD nm qs op e prems) = false)
    (hgE : ElseBwd.goodRuleE (.ruleD nm qs op e prems) = false)
    (hgN : BadN.goodRuleN (.ruleD nm qs op e prems) = false) : nm ∈ badNames := by
  rw [findRel?_utf8Env] at hrel
  have hm := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 badNames_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simp only [hg, hgE, hgN, Bool.false_or, ruleName, List.contains_iff_mem] at h'
  exact h'

/-- **`BadFwdN` from the seven rules.** -/
theorem badFwdN_of_rules {B : Builtins} (h : ∀ nm ∈ badNames, RuleFwdNm (utf8Env B) nm) :
    BadN.BadFwdN (utf8Env B) := by
  intro x op args i v hx ⟨ps, t, rules, nm, qs, e, e', prems, ρ₀, σ, hrel, hrule, hg, hgE, hgN,
    halt, hps, hq, he, hp⟩
  exact h nm (mem_badNames hx hrel hrule hg hgE hgN) hx hrel hrule halt hps hq he hp

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
