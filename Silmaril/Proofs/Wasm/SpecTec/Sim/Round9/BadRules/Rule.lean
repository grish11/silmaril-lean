module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.BadN.Rule

/-!
# Round 9, RE: the rule case with some premises and the conclusion supplied

`ruleFwdX` is `BadN.ruleFwdN` (the rule case at a rule passing `goodRuleN`) with the conclusion and
the premises failing `BadN.premN` supplied on the erased side by the caller. `concl_fwd`: a
conclusion alternative passing round 3's syntactic check goes to the erased side.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.NxDer (PCtx)
open Silmaril.Wasm.SpecTec.Sim.Round9.BadN
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

variable {B : Builtins}

section Rule

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **A conclusion alternative passing round 3's check goes to the erased side.** -/
theorem concl_fwd {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem} {σ : List (IL.Id × Value)}
    {v : Value} (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hq : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
    (hxe : xExp grE gdE e' = true) (he : EvalExp (utf8Env B) (VarEnv.empty.bindVals σ) e' v) :
    EvalExp (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e' (eraseV v) := by
  have hr : reach 0 x = true := Round8.NxStep.reach_stepRel hx
  have hD := NxFlow.flowSound B hB
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  obtain ⟨n, hn⟩ := he
  refine ⟨n, ?_⟩
  rw [NxErase.erase_alt hD H hr hrel hrule hq hCE halt hxe n, hn]
  rfl

/-- **The rule case, with the conclusion and the premises failing `premN` supplied.** -/
theorem ruleFwdX {x : IL.Id} {op : MixopS} {args : List ArgV} {i : Nat} {v : Value}
    {ps : List Param} {t : Typ} {rules : List Rule} {nm : IL.Id} {qs : List Param} {e e' : Exp}
    {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hps : bindParams VarEnv.empty ps args = some ρ₀)
    (hq : QuantsOk (utf8Env B) (ρ₀.bindVals σ) qs)
    (hconcl : ρ₀ = VarEnv.empty →
      EvalExp (utf8Env B) (eraseScope (ρ₀.bindVals σ)) e' (eraseV v))
    (hp : ∀ pr ∈ prems, premN pr = true → DPremB (utf8Env B) (otherwiseB (utf8Env B))
      (otherwiseB (utf8Env B) x args i v) (ρ₀.bindVals σ) pr)
    (hbad : ∀ pr ∈ prems, premN pr = false → ρ₀ = VarEnv.empty → args = [] →
      DPremB (utf8Env B) (otherwiseB (utf8Env B))
        (otherwiseB (utf8Env B) x [] i (eraseV v)) (eraseScope (ρ₀.bindVals σ)) pr) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map eraseA) (eraseV v) := by
  have hr : reach 0 x = true := Round8.NxStep.reach_stepRel hx
  have hF := NxRule.rFacts hr hrel hrule
  obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
  have hq' : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs := hρ ▸ hq
  have heq : ρ₀.bindVals (σ.map eraseP) = eraseScope (ρ₀.bindVals σ) := by
    rw [hρ, Round8.NxDer.eraseScope_inst]
  have hD := NxFlow.flowSound B hB
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  have hC : PCtx B (quantsΓ qs) (qScope qs (ρ₀.bindVals σ)) := by
    rw [hρ]
    exact ⟨NxRule.scopeVT_qScope (NxRule.typsNx_inst σ) hq' hF.wild,
      fun n => ⟨NxRule.callH_nil hD rfl rfl n, hCE n, fun p hp => by
        simp [qScope, VarEnv.bindVals, VarEnv.empty, Map.empty] at hp⟩⟩
  have hX := NxErase.ruleX_at hr hrel (List.mem_of_getElem? hrule)
  simp only [NxErase.ruleX, Bool.and_eq_true, List.all_eq_true] at hX
  have hps' : bindParams VarEnv.empty ps (args.map eraseA) = some ρ₀ := by
    rw [hargs]; rw [hargs] at hps; exact hps
  refine .rule (σ := σ.map eraseP) hrel hrule halt hps' ?_ ?_ fun pr hpr => ?_
  · rw [hρ, ← Round8.NxDer.eraseScope_inst]
    exact Round8.NxTyp.typFwdN_utf8Env hr hrel hrule hq'
  · rw [heq]
    exact hconcl hρ
  · rw [heq]
    cases hN : premN pr with
    | false =>
      have h := hbad pr hpr hN hρ hargs
      rw [hargs]
      exact h
    | true =>
    have hp := hp pr hpr hN
    obtain ⟨hpt, hpa, hpc⟩ := hF.premsOk pr hpr
    by_cases hif : ∃ c, pr = .ifPr c
    · obtain ⟨c, rfl⟩ := hif
      have hxc : xExp grE gdE c = true := by
        simp only [premN, Round8.NxStep.premS, EraseAll.xPrem, iterN, ElseBwd.stepPremB,
          Bool.and_eq_true, Bool.or_eq_true, Bool.false_and] at hN
        rcases hN with h | h
        · exact h.1.1.1
        · cases h
      cases hp with
      | ifPr h =>
        rw [hρ] at h ⊢
        exact .ifPr (NxClause.ifPr_fwd hD H hr hrel hrule hq' hCE hpr hxc h)
    · have hbs : bindSite sigX (quantsΓ qs) pr = false := by
        cases pr with
        | ifPr c => exact absurd ⟨c, rfl⟩ hif
        | _ => rfl
      have hb := NxRule.badPr_zero hr hrel hrule hpr hbs
      simp only [premN, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hN
      rcases hN with ⟨hS, hns⟩ | ⟨hin, hxp⟩
      · have hS' := Round8.NxStep.premS_other hS fun y args' op' e₁ h => by
          subst h; simpa [ElseBwd.stepPremB] using hns
        have hfire := Round8.NxElse.dpremB_fire (els' := otherwiseB (utf8Env B) x
          (args.map eraseA) i (eraseV v)) hS'.1 (fun h => by rw [hS'.2.2] at h; cases h) hp
        exact Round8.NxDer.dpremB_fwd hB H (Round8.NxElse.hO_else hB H) hC
          (NxRule.agreeOn_qScope hpc) hpt hpa (hX.2 pr hpr) hb hS'.1 hS'.2.1 id hfire
      · obtain ⟨pr', eₙ, ido, ds, rfl, hl, hne⟩ := iterN_inv hin
        have hfire := Round8.NxElse.dpremB_fire (els' := otherwiseB (utf8Env B) x
          (args.map eraseA) i (eraseV v)) hxp
          (fun h => by simp only [Round8.NxElse.elseIn, hne] at h; cases h) hp
        exact iterN_fwd hB H (Round8.NxElse.hO_else hB H) hC (NxRule.agreeOn_qScope hpc) hpt hpa
          (hX.2 _ hpr) hb hxp hl id hfire

end Rule

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
