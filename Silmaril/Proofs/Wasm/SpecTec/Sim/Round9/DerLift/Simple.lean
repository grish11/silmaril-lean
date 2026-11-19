module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.DerLift.Induct
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.Thms

/-!
# Round 9, REH: the backward lift at the `Step_read` rules that rebind only their state

`ruleLift_simple`: `RuleLift` at every rule of `Step_read` that passes `liftSimple`, for every
provenance `Prov` under which the state of a `Step_read` input is typed (`state`).

The erased instance `σ₀` evaluates the conclusion `(z; L, R)` to `(eraseV a, b₀)`. So
`a = (zv; lv)` with `eraseV zv = σ₀ z` and `eraseV lv = L(σ₀)`. `L` reads only export-free
quantifiers and is export-free (`NxSites.nxE`, read by round 7's flow soundness
`NxRule.eOk_of_closed`), so `L(σ₀)` has no export list and `lv = L(σ₀)`. The instance
`σ := σ₀, z := zv` **rebinds `z` positionally**, to the state of `a`; every other quantifier
keeps its (export-free) value. Then:

* `σ` is typed: `zv` by the provenance, the others as in `σ₀` (`NxTyp.hasTyp_fwd`).
* `eraseScope σ` agrees with `σ₀`, so round 7's equations (`NxErase.erase_alt`,
  `NxErase.erase_ifPr`) give the conclusion `(a, b)` with `eraseV b = b₀` and every `if`.
* `otherwise`, if present, is read backward by `ElseLift.otherwiseAtB_lift_read`.

The successor `b` is the one this instance computes; nothing is chosen through Core.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB otherwiseAtB)

variable {B : Builtins}

/-- The erasure of a configuration value `z; L` is one. -/
theorem eraseV_cfg_inv {a zv₀ lv₀ : Value} (h : eraseV a = .case "%;%" (.tuple [zv₀, lv₀])) :
    ∃ zv lv, a = .case "%;%" (.tuple [zv, lv]) ∧ eraseV zv = zv₀ ∧ eraseV lv = lv₀ := by
  match a, h with
  | .case op (.tuple [zv, lv]), h =>
    simp only [eraseV, eraseVs, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      and_true] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨zv, lv, rfl, rfl, rfl⟩
  | .case _ (.tuple []), h | .case _ (.tuple [_]), h | .case _ (.tuple (_ :: _ :: _ :: _)), h =>
    simp [eraseV, eraseVs] at h
  | .case _ (.opt none), h | .case _ (.opt (some _)), h | .case _ (.bool _), h
  | .case _ (.num _), h | .case _ (.text _), h | .case _ (.list _), h | .case _ (.case _ _), h
  | .case _ (.struct _), h => simp [eraseV] at h
  | .opt none, h | .opt (some _), h | .bool _, h | .num _, h | .text _, h | .tuple _, h
  | .list _, h | .struct _, h => simp [eraseV] at h

/-- An export-free value is the only preimage of its erasure. -/
theorem eq_of_eraseV_nxB {v w : Value} (h : eraseV v = w) (hw : nxB w = true) : v = w := by
  have hv : nxB v = true := by rw [← NxSites.nxB_eraseV, h]; exact hw
  rw [← Swap.eraseV_of_nxB v hv, h]

theorem varsIn_mono {K K' : List IL.Id} (hK : ∀ x ∈ K, x ∈ K') {s : Sets}
    (h : EraseDer.varsIn K s = true) : EraseDer.varsIn K' s = true := by
  unfold EraseDer.varsIn at h ⊢
  have h' := of_decide_eq_true h
  exact decide_eq_true fun x hx => hK x (h' x hx)

theorem nxNames_sub {qs : List Param} : ∀ x ∈ Round8.NxTyp.nxNames qs, x ∈ quantNames qs := by
  intro x hx
  simp only [Round8.NxTyp.nxNames, List.mem_filterMap] at hx
  obtain ⟨q, hq, hx⟩ := hx
  cases q with
  | expP y t =>
    simp only at hx
    split at hx
    · cases hx
      simp only [quantNames, List.mem_filterMap]
      exact ⟨_, hq, rfl⟩
    · cases hx
  | _ => cases hx

section Simple

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  (hP : ElseBwdB (utf8Env B))
include hB H hP

set_option maxRecDepth 20000 in
/-- **`RuleLift` at the `Step_read` rules that pass `liftSimple`**, for every provenance that
types the state of a `Step_read` input. -/
theorem ruleLift_simple {Prov : IL.Id → Value → Prop}
    (hZ : ∀ a zv lv, Prov "Step_read" a → a = .case "%;%" (.tuple [zv, lv]) →
      HasTyp (utf8Env B) VarEnv.empty (.varT "state" []) zv)
    {i : Nat} (hs : ∀ ps op t rules r, (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules) →
      rules[i]? = some r → liftSimple r = true) :
    RuleLift (utf8Env B) (otherwiseB (utf8Env B)) Prov "Step_read" i := by
  intro op args v₀ ps t rules nm qs e e' prems ρ₀ σ' hrel hrule halt hps hq' hev' hpr' a b₀ hv₀ hpa
  have hrd : reach 0 "Step_read" = true := by decide
  have hsr : Script.stepReach.contains (0, "Step_read") = true := by decide
  have hD := NxFlow.flowSound B hB
  have hFj := NxRule.rFacts hrd hrel hrule
  obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hFj.params ▸ hps)
  subst hρ hargs
  have hsl := hs ps op t rules _ hrel hrule
  simp only [liftSimple, Bool.and_eq_true, List.all_eq_true] at hsl
  obtain ⟨hsj, hll⟩ := hsl
  have hsj' := hsj
  simp only [simpleRuleE, Bool.and_eq_true, List.all_eq_true] at hsj'
  obtain ⟨hsc, hsp⟩ := hsj'
  have hsc' := hsc e' halt
  have hll' := hll e' halt
  split at hsc'
  case h_2 => cases hsc'
  rename_i z l hcfg
  rw [hcfg] at hll'
  simp only [Bool.and_eq_true] at hll'
  obtain ⟨⟨hlt, hla⟩, hlnx⟩ := hll'
  simp only [Bool.and_eq_true] at hsc'
  obtain ⟨⟨hok, hqn⟩, hxe⟩ := hsc'
  obtain ⟨z', l', hcfg', hsq, hl, hzn⟩ := ElseBwd.lhsOk_parts hok
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨r0, rfl⟩ := cfgVar_some hcfg
  -- the erased instance
  obtain ⟨n, hn⟩ := hev'
  obtain ⟨k, zv₀, lv₀, rv₀, hk, hw, hz₀, hl₀⟩ := eval_cfg hn
  subst hw
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv₀
  obtain ⟨ha₀, rfl⟩ := hv₀
  obtain ⟨zv, lv, rfl, hzv, hlv⟩ := eraseV_cfg_inv ha₀.symm
  -- `L` is export-free, so the original instructions are its erased value
  have hlnxB : nxB lv₀ = true :=
    NxRule.nxB_of_eOk
      (NxRule.eOk_of_closed hD hq' hFj.wild (varsIn_mono nxNames_sub hl) hlt hla ⟨k, hl₀⟩) hlnx
  have hlv' : lv = lv₀ := eq_of_eraseV_nxB hlv hlnxB
  subst hlv'
  have hzt := hZ _ zv lv hpa rfl
  -- the new instance: `z` rebound to the original state
  have hzw : z ≠ "_" := fun h => hFj.wild (h ▸ stateQ_mem hsq)
  let σj := σ' ++ [(z, zv)]
  have hfz : (VarEnv.empty.bindVals σj).findVal? z = some zv := findVal_snoc_self hzw zv
  have hfo : ∀ y, y ≠ z → (VarEnv.empty.bindVals σj).findVal? y =
      (VarEnv.empty.bindVals σ').findVal? y := fun y hy => findVal_snoc_ne hy zv
  have hnx : ∀ y ty, Param.expP y ty ∈ qs → y ≠ z → Round8.NxTyp.nxT ty = true := by
    intro y ty hy hyz
    simp only [quantsNx, List.all_eq_true] at hqn
    have := hqn _ hy
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left hyz
  have hval : ∀ y ty, Param.expP y ty ∈ qs → y ≠ z → ∃ w,
      (VarEnv.empty.bindVals σ').findVal? y = some w ∧ nxB w = true := fun y ty hy hyz =>
    NxSites.nxB_of_quantsOk (NxSites.typsNx_bindVals (NxSites.typsNx_empty _) σ') hq' hy
      (hnx y ty hy hyz)
  have hagr : Round8.NxTyp.Agr (Round8.NxTyp.nxNames qs) (VarEnv.empty.bindVals σ')
      (VarEnv.empty.bindVals σj) :=
    ⟨fun y hy => hfo y (fun h => hzn (h ▸ hy)), rfl, rfl, rfl⟩
  have hqj : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σj) qs := by
    intro y ty hy
    by_cases hyz : y = z
    · subst hyz
      have := stateQ_type hsq hy
      subst this
      exact ⟨zv, hfz, hasTyp_varT_scope rfl rfl hzt⟩
    · obtain ⟨w, hw, hty⟩ := hq' y ty hy
      obtain ⟨w', hw', hnw⟩ := hval y ty hy hyz
      rw [hw] at hw'
      cases hw'
      refine ⟨w, (hfo y hyz).trans hw, ?_⟩
      have h := Round8.NxTyp.hasTyp_fwd Round8.NxTyp.envN_utf8Env (NxSites.envNx_utf8Env B) hagr
        (Round8.NxTyp.typsTP_inst σ') (Round8.NxTyp.nTy_quant hsr hrel hrule hy) hty
      rwa [Swap.eraseV_of_nxB _ hnw] at h
  -- the erased new instance agrees with `σ'` on the quantifiers
  have hag : ∀ s, EraseDer.varsIn (quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals σj)) (VarEnv.empty.bindVals σ') := by
    intro s hs
    refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [Erase.find?_eraseScope]
    by_cases hyz : y = z
    · subst hyz; rw [hfz, hz₀]; simp [hzv]
    · obtain ⟨ty, hty⟩ := mem_quantNames (EraseDer.varsIn_mem hs y hy)
      obtain ⟨w, hw, hnw⟩ := hval y ty hty hyz
      rw [hfo y hyz, hw]
      simp [Swap.eraseV_of_nxB _ hnw]
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σj)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  -- the conclusion on the original side
  have hE := NxErase.erase_alt hD H hrd hrel hrule hqj hCE halt hxe n
  rw [evalExp_agreeOn (hag _ (hFj.alts _ halt).2), hn] at hE
  obtain ⟨u, hu, hue⟩ := map_eq_ok hE.symm
  obtain ⟨k₂, zv₂, lv₂, rv₂, hk₂, rfl, hz₂, hl₂⟩ := eval_cfg hu
  have hkk : k₂ = k := by omega
  subst hkk
  rw [hfz] at hz₂
  cases hz₂
  have hagl : VarEnv.AgreeOn (freeExp l) (VarEnv.empty.bindVals σ') (VarEnv.empty.bindVals σj) :=
    Round8.NxElse.agreeOn_of_agr hagr hl
  rw [← evalExp_agreeOn hagl, hl₀] at hl₂
  cases hl₂
  have hrv : eraseV rv₂ = rv₀ := by
    simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq, and_true] at hue
    exact hue.2
  refine ⟨rv₂, .rule hrel hrule halt hps hqj ⟨n, hu⟩ fun pr hpr => ?_, hrv⟩
  -- the premises on the original side
  have hspr := hsp pr hpr
  split at hspr
  case h_3 => cases hspr
  case h_2 =>
    cases hpr' _ hpr with
    | elsePr h =>
      have hFi : Round8.NxElse.Fired (utf8Env B) "Step_read" [] i
          (.tuple [eraseV (.case "%;%" (.tuple [zv, lv])), rv₀]) := by
        refine ⟨ps, op, t, rules, nm, qs, e, prems, _, VarEnv.empty, σ', hrel, hrule,
          elseIn_of_mem hpr, halt, hps, hq', ⟨n, ?_⟩⟩
        rw [hn, ha₀]
      have h' : otherwiseAtB (utf8Env B) "Step_read" [] i
          (.tuple [eraseV (.case "%;%" (.tuple [zv, lv])), rv₀]) := by
        rw [← ha₀]
        exact h
      exact .elsePr (ElseLift.otherwiseAtB_lift_read (ElseLift.elseFwdB_of hB H hP) hrel hrule
        (fun _ hj _ hrj hd => elsePairs_mem hrel hrule (hasElse_of_mem hpr) hj hrj hd) hFi h' rv₂)
  rename_i c₀
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hspr
  obtain ⟨hxc, hbs⟩ := hspr
  cases hpr' _ hpr with
  | ifPr h =>
    obtain ⟨n₀, hn₀⟩ := h
    have hE₀ := NxErase.erase_ifPr hD H hrd hrel hrule hqj hCE hpr hbs hxc n₀
    rw [evalExp_agreeOn (hag _ (hFj.premsOk _ hpr).2.2), hn₀] at hE₀
    obtain ⟨u₀, hu₀, hue₀⟩ := map_eq_ok hE₀.symm
    exact .ifPr ⟨n₀, by rw [hu₀, eraseV_eq_bool hue₀]⟩

end Simple

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
