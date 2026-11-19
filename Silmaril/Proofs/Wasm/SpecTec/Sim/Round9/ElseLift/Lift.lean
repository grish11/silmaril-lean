module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseLift.Check
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms

/-!
# Round 9, REH: SpecTec's `otherwise` read backward along export erasure

* `otherwiseAtB_lift`: at a rule `i` that fires on the erased side at `(eraseV a, b₀)`, SpecTec's
  `otherwise` there gives it at `(a, b)` for every `b`, from the real ordered-rule definition
  (`Round6.Reading.otherwiseAtB`): an earlier rule `j` that fired at `(a, c)` either has a head
  different from rule `i`'s (and erasure keeps heads, `ElseBwd.vHead_eraseV`), or `(i, j)` is a
  pair of `ElseBwd.elsePairs`, where it fires forward at `(eraseV a, c')` (`PairFireFwdB`), which
  the erased side excludes.
* `fireFwd_goodE`: a rule of `Step_read` that passes `ElseBwd.goodRuleE` fires forward along
  erasure under `otherwise`'s reading (premises by `DDerivesB env noElse`, its own `otherwise` by
  `otherwiseAtB`), given `ElseBwd.ElseBwdB` for its own `otherwise`. This is round 9's
  `ElseBwd.ruleFwdE` at a rule body: the premises are moved by round 8's `NxDer.dpremB_fwd` at
  the reading `noElse`, where its hypothesis on `otherwise` is vacuous.
* `elseFwdB_of`, `elseFwdB_BI`: `ElseFwdB` (all 94 pairs), from the kernel check
  `fwdPairs_fixed`; at round 4's primitives with no hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0 premAuxR)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT premX)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp xPrem eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.NxDer (PCtx)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB DPremB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

/-! ## Small facts -/

theorem headNe_comm (e₁ e₂ : Exp) : headNe e₁ e₂ = headNe e₂ e₁ := by
  unfold headNe
  cases lhsHead e₁ <;> cases lhsHead e₂ <;> simp [bne_comm]

/-- A premise without `otherwise` does not read the `otherwise` proposition. -/
theorem dpremB_els {env : Env} {O : ElseI} {els els' : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, Round8.NxElse.elseIn pr = false → DPremB env O els ρ pr →
      DPremB env O els' ρ pr
  | _, _, _, .ifPr h => .ifPr h
  | _, _, he, .elsePr _ => by simp [Round8.NxElse.elseIn] at he
  | _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, _, .rulePr ha he hd => .rulePr ha he hd
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, he, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremB_els he hp)
  | _, _, he, .iterList hit hd hne hl hk hp =>
    .iterList hit hd hne hl hk fun r hr => dpremB_els he (hp r hr)
  | _, _, he, .iterListN hd hev hk hl hlen hp =>
    .iterListN hd hev hk hl hlen fun r hr => dpremB_els he (hp r hr)

/-! ## The backward `otherwise` -/

/-- **SpecTec's `otherwise` read backward along export erasure.** Rule `i` of `x` fires on the
erased side at `(eraseV a, b₀)` and its `otherwise` holds there. Given the forward firing of the
earlier rules whose heads are not known to differ (`PairFireFwdB`), its `otherwise` holds at
`(a, b)`, for every `b`. -/
theorem otherwiseAtB_lift {env : Env} {x : IL.Id} {i : Nat} {a b₀ : Value}
    (hF : Round8.NxElse.Fired env x [] i (.tuple [eraseV a, b₀]))
    (hR : ∀ j < i, ∀ ps op t rules ri rj, env.findRel? x = some (ps, op, t, rules) →
      rules[i]? = some ri → rules[j]? = some rj → headsDiffer ri rj = false →
      PairFireFwdB env eraseV x i j)
    (h : otherwiseAtB env x [] i (.tuple [eraseV a, b₀])) (b : Value) :
    otherwiseAtB env x [] i (.tuple [a, b]) := by
  rw [otherwiseAtB] at h ⊢
  intro j hj ps op t rules r hrel hr w hw hbody
  obtain ⟨a₁, b₁, c, hv, rfl⟩ := hw
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, -⟩ := hv
  have hF' := hF
  obtain ⟨ps', op', t', rules', nm, qs, e, prems, e', ρ₀, σ, hrel', hrule, -, halt, -, -, hev⟩ := hF'
  rw [hrel] at hrel'
  cases hrel'
  obtain ⟨nmj, qsj, opj, ej, premsj⟩ := r
  cases hd : headsDiffer (.ruleD nm qs op e prems) (.ruleD nmj qsj opj ej premsj) with
  | true =>
    obtain ⟨ej', haltj, -, ρ₂, σ₂, -, -, hevj, -⟩ := hbody
    have hne := headsDiffer_alt hd halt haltj
    rw [headNe_comm] at hne
    exact heads_clash (ε := eraseV) vHead_eraseV (b' := eraseV c) (by simp [eraseV, eraseVs])
      hevj hev hne
  | false =>
    obtain ⟨c', hc'⟩ := hR j hj ps op t rules _ _ hrel hrule hr hd ps op t rules _ hrel hr a b₀ c
      hF hbody
    exact h j hj ps op t rules _ hrel hr _ ⟨eraseV a, b₀, c', rfl, rfl⟩ hc'

/-! ## Forward firing of the earlier rules -/

theorem fwdPairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ elsePairs) : ∃ rj, rules[j]? = some rj ∧ goodRuleE rj = true := by
  rw [findRel?_utf8Env] at hrel
  have hmem := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 fwdPairs_fixed _ hmem
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h
  have h' := h _ hij
  split at h'
  · rename_i rj hrj
    exact ⟨rj, hrj, h'⟩
  · cases h'

section Fwd

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  (hP : ElseBwdB (utf8Env B))
include hB H hP

set_option maxRecDepth 20000 in
/-- **A `Step_read` rule that passes `goodRuleE` fires forward along erasure**, under SpecTec's
reading of `otherwise` (premises by `DDerivesB env noElse`, its own `otherwise` by
`otherwiseAtB`). -/
theorem fireFwd_goodE {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {k : Nat}
    {nm : IL.Id} {qs : List Param} {opk : MixopS} {e : Exp} {prems : List Prem} {w : Value}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hrk : rules[k]? = some (.ruleD nm qs opk e prems))
    (hg : goodRuleE (.ruleD nm qs opk e prems) = true)
    (hbody : RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] k w) ps [] op (.ruleD nm qs opk e prems) w) :
    RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) Sim.noElse)
      (otherwiseAtB (utf8Env B) "Step_read" [] k (eraseV w)) ps [] op
      (.ruleD nm qs opk e prems) (eraseV w) := by
  simp only [goodRuleE, Bool.and_eq_true, List.all_eq_true] at hg
  have hr : reach 0 "Step_read" = true := by decide
  have hsr : Script.stepReach.contains (0, "Step_read") = true := by decide
  have hD := NxFlow.flowSound B hB
  have hF := NxRule.rFacts hr hrel hrk
  obtain ⟨e', halt, hop, ρ₀, σ, hps, hq, ⟨n, hn⟩, hpr⟩ := hbody
  obtain ⟨-, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
  subst hρ
  subst hop
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  have hC : PCtx B (quantsΓ qs) (qScope qs (VarEnv.empty.bindVals σ)) :=
    ⟨NxRule.scopeVT_qScope (NxRule.typsNx_inst σ) hq hF.wild,
      fun n => ⟨NxRule.callH_nil hD rfl rfl n, hCE n, fun p hp => by
        simp [qScope, VarEnv.bindVals, VarEnv.empty, Map.empty] at hp⟩⟩
  have hX := NxErase.ruleX_at hr hrel (List.mem_of_getElem? hrk)
  simp only [NxErase.ruleX, Bool.and_eq_true, List.all_eq_true] at hX
  refine ⟨e', halt, rfl, VarEnv.empty, σ.map eraseP, hps, ?_, ⟨n, ?_⟩, fun pr hp => ?_⟩
  · rw [← Round8.NxDer.eraseScope_inst]
    exact Round8.NxTyp.typFwdN_utf8Env hsr hrel hrk hq
  · rw [← Round8.NxDer.eraseScope_inst,
      NxErase.erase_alt hD H hr hrel hrk hq hCE halt (hg.1 _ halt) n, hn]
    rfl
  · rw [← Round8.NxDer.eraseScope_inst]
    have hpd := Determ.premW_dpremB (hpr pr hp)
    refine Determ.dpremB_premW ?_
    rcases premSE_cases (hg.2 pr hp) with rfl | ⟨hS, hns⟩
    · cases hpd with
      | elsePr h =>
        have hFk : Round8.NxElse.Fired (utf8Env B) "Step_read" [] k w :=
          ⟨ps, _, t, rules, nm, qs, e, prems, e', VarEnv.empty, σ, hrel, hrk, elseIn_of_mem hp,
            halt, hps, hq, ⟨n, hn⟩⟩
        refine .elsePr (otherwiseAtB_map (fun _ _ _ => eraseV_pair) vHead_eraseV hFk ?_ h)
        intro m hm ps₂ op₂ t₂ rules₂ ri rm hrel₂ hri hrm hd
        rw [hrel] at hrel₂
        cases hrel₂
        rw [hrk] at hri
        cases hri
        exact hP (k, m) (elsePairs_mem hrel hrk (hasElse_of_mem hp) hm hrm hd)
    obtain ⟨hpt, hpa, hpc⟩ := hF.premsOk pr hp
    by_cases hif : ∃ c, pr = .ifPr c
    · obtain ⟨c, rfl⟩ := hif
      have hxc : xExp grE gdE c = true := by
        simp only [Round8.NxStep.premS, xPrem, Bool.and_eq_true] at hS
        exact hS.1.1
      cases hpd with
      | ifPr h => exact .ifPr (NxClause.ifPr_fwd hD H hr hrel hrk hq hCE hp hxc h)
    · have hbs : bindSite sigX (quantsΓ qs) pr = false := by
        cases pr with
        | ifPr c => exact absurd ⟨c, rfl⟩ hif
        | _ => rfl
      have hb := NxRule.badPr_zero hr hrel hrk hp hbs
      have hS' := Round8.NxStep.premS_other hS fun y args' op' e₁ h => by
        subst h; simpa [stepPremB] using hns
      have hpd' : DPremB (utf8Env B) Sim.noElse False (VarEnv.empty.bindVals σ) pr :=
        dpremB_els hS'.2.2 hpd
      exact Round8.NxDer.dpremB_fwd hB H (O₁ := Sim.noElse) (O' := Sim.noElse)
        (fun _ _ _ _ h => h) hC (NxRule.agreeOn_qScope hpc) hpt hpa (hX.2 pr hp) hb hS'.1
        hS'.2.1 False.elim hpd'

/-- **`PairFireFwdB` at every pair of `elsePairs`.** -/
theorem elseFwdB_of : ElseFwdB (utf8Env B) := by
  intro p hp ps op t rules r hrel hr a b₀ c _ hbody
  obtain ⟨rj, hrj, hg⟩ := fwdPairs_at hrel hp
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opk, e, prems⟩ := r
  have h := fireFwd_goodE hB H hP hrel hr hg hbody
  simp only [eraseV, eraseVs] at h
  exact ⟨eraseV c, h⟩

end Fwd

/-- **`ElseFwdB` at round 4's primitives**, with no hypothesis. -/
theorem elseFwdB_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) : ElseFwdB (NxPrims.envBI P hn host) :=
  elseFwdB_of (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host)
    (ElseRef.elseBwdB_BI P hn host)

/-- **SpecTec's `otherwise` of `Step_read` read backward along export erasure**, given
`ElseFwdB`: at an `otherwise` rule `i` that fired on the erased side at `(eraseV a, b₀)`. -/
theorem otherwiseAtB_lift_read {env : Env} (hE : ElseFwdB env) {i : Nat} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {ri : Rule}
    (hrel : env.findRel? "Step_read" = some (ps, op, t, rules)) (hri : rules[i]? = some ri)
    (hpairs : ∀ j < i, ∀ rj, rules[j]? = some rj → headsDiffer ri rj = false →
      (i, j) ∈ elsePairs)
    {a b₀ : Value} (hF : Round8.NxElse.Fired env "Step_read" [] i (.tuple [eraseV a, b₀]))
    (h : otherwiseAtB env "Step_read" [] i (.tuple [eraseV a, b₀])) (b : Value) :
    otherwiseAtB env "Step_read" [] i (.tuple [a, b]) := by
  refine otherwiseAtB_lift hF (fun j hj ps' op' t' rules' ri' rj hrel' hri' hrj hd => ?_) h b
  rw [hrel] at hrel'
  cases hrel'
  rw [hri] at hri'
  cases hri'
  exact hE (i, j) (hpairs j hj rj hrj hd)

/-- **SpecTec's `otherwise` of `Step_read` read backward along export erasure, at round 4's
primitives**, with no hypothesis: at every `otherwise` rule `i` of `Step_read` that fired on the
erased side at `(eraseV a, b₀)` with its `otherwise` true there, its `otherwise` holds at
`(a, b)`. -/
theorem otherwiseAtB_lift_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {i : Nat} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {ri : Rule}
    (hrel : (NxPrims.envBI P hn host).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hel : hasElse ri = true) {a b₀ : Value}
    (hF : Round8.NxElse.Fired (NxPrims.envBI P hn host) "Step_read" [] i (.tuple [eraseV a, b₀]))
    (h : otherwiseAtB (NxPrims.envBI P hn host) "Step_read" [] i (.tuple [eraseV a, b₀]))
    (b : Value) : otherwiseAtB (NxPrims.envBI P hn host) "Step_read" [] i (.tuple [a, b]) :=
  otherwiseAtB_lift_read (elseFwdB_BI P hn host) hrel hri
    (fun _ hj _ hrj hd => elsePairs_mem hrel hri hel hj hrj hd) hF h b

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift
