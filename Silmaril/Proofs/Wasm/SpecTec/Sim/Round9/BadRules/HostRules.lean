module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadRules.GrowRules
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.HostRule

/-!
# Round 9, RE: the host-call rules go to the erased side at export-blind hosts

`call_ref-hostfunc-res` and `call_ref-hostfunc-div` have premises `ps ++ [pat <- $hostcall(e₁,
s, e₃)]` with `ps` passing `BadN.premN`, and a conclusion passing round 3's check (kernel check
`hostShapeN_fixed`). Only the `$hostcall` premise is left. It goes across as in round 7's
`EraseDer.ruleFwd_host`, without the swap set:

* the arguments are the image of a host call at some store `s₀`; their erasure is the image of the
  same call at `stripStore s₀` (`Swap.eraseA_hostArgs`);
* that image is typed `store` on the erased side (route 2's `typFwdN_utf8Env`) and export-free,
  so it has one preimage (`EraseDer.storeV_uniq_typed`), and `$hostcall` lists exactly the host's
  outcomes there (`Swap.hostcallCall_at`, for an injective naming and a finite host);
* the first half of `HostExportBlind` puts the stripped outcome among them, and the erased value
  of `pat` is its image (`Swap.eraseV_outcomeV`).

Hence `ruleFwd_host`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadRules

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA eraseVs_eq_map)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grE gdE xExp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

/-! ## The shape, checked by the kernel -/

/-- **The shape of the host-call rules**: a conclusion passing round 3's check, and premises
`ps ++ [pat <- $hostcall(e₁, s, e₃)]` with `ps` passing `BadN.premN`, `pat`, `e₁`, `e₃` passing
every check of the erasure, and `s : store`. -/
def hostShapeN : Rule → Bool
  | .ruleD _ qs _ e prems =>
    (conclAlts e).all (xExp grE gdE) &&
    match prems.getLast? with
    | some (.ifPr (.memE pat (.callE "hostcall" [.expA e₁, .expA (.varE z), .expA e₃]))) =>
      prems.dropLast.all BadN.premN && closedOk qs pat && closedOk qs e₁ && closedOk qs e₃ &&
        hasQ qs z "store"
    | _ => false

/-- The two host-call rules. -/
def hostNamesN : List String := ["call_ref-hostfunc-res", "call_ref-hostfunc-div"]

set_option maxRecDepth 100000 in
/-- **The host-call rules have the shape.** -/
theorem hostShapeN_fixed : (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).all (fun p =>
    !Round8.NxStep.stepRel p.1 || p.2.2.2.2.all fun r =>
      !hostNamesN.contains (ruleName r) || hostShapeN r) = true := by
  decide +kernel

/-- The `$hostcall` premise. -/
def hostPrN (pat e₁ : Exp) (z : IL.Id) (e₃ : Exp) : Prem :=
  .ifPr (.memE pat (.callE "hostcall" [.expA e₁, .expA (.varE z), .expA e₃]))

/-- What `hostShapeN` says. -/
structure HostFactsN (qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  alts : ∀ e' ∈ conclAlts e, xExp grE gdE e' = true
  shape : ∃ ps pat e₁ z e₃, prems = ps ++ [hostPrN pat e₁ z e₃] ∧
    (∀ pr ∈ ps, BadN.premN pr = true) ∧ closedOk qs pat = true ∧ closedOk qs e₁ = true ∧
    closedOk qs e₃ = true ∧ Param.expP z (.varT "store" []) ∈ qs

theorem hostShapeN_inv {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : hostShapeN (.ruleD nm qs op e prems) = true) :
    HostFactsN qs e prems := by
  simp only [hostShapeN, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨ha, h⟩ := h
  refine ⟨ha, ?_⟩
  split at h
  · rename_i pat e₁ z e₃ hl
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hp, hpat⟩, h₁⟩, h₃⟩, hz⟩ := h
    refine ⟨prems.dropLast, pat, e₁, z, e₃, ?_, hp, hpat, h₁, h₃, hasQ_mem hz⟩
    exact (List.dropLast_append_getLast? _ hl).symm
  · cases h

theorem hostFactsN {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hnm : nm ∈ hostNamesN) :
    HostFactsN qs e prems := by
  rw [findRel?_utf8Env] at hrel
  have hm := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 hostShapeN_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simp only [ruleName, List.contains_iff_mem.2 hnm, Bool.not_true, Bool.false_or] at h'
  exact hostShapeN_inv h'

/-! ## The `$hostcall` premise -/

theorem evalArgs3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {a b c : Value}
    (h : EvalArgs env ρ [.expA e₁, .expA e₂, .expA e₃] [.val a, .val b, .val c]) :
    EvalExp env ρ e₁ a ∧ EvalExp env ρ e₂ b ∧ EvalExp env ρ e₃ c := by
  obtain ⟨k, h⟩ := h
  cases k with
  | zero => simp [evalArgs] at h
  | succ k =>
    simp only [evalArgs, List.mapM_cons, List.mapM_nil, Res.bind_eq_ok, pure, Except.pure] at h
    obtain ⟨a₁, h₁, l₁, ⟨a₂, h₂, l₂, ⟨a₃, h₃, l₃, hl₃, hl₂⟩, hl₁⟩, hws⟩ := h
    cases Except.ok.inj hl₃
    cases Except.ok.inj hl₂
    cases Except.ok.inj hl₁
    simp only [Except.ok.injEq, List.cons.injEq, and_true] at hws
    obtain ⟨rfl, rfl, rfl⟩ := hws
    refine ⟨?_, ?_, ?_⟩ <;>
    · rcases k with _ | k
      · simp [evalArg] at *
      · simp only [evalArg, Res.map_eq_ok] at h₁ h₂ h₃
        first
          | (obtain ⟨v, hv, hve⟩ := h₁; cases hve; exact ⟨k, hv⟩)
          | (obtain ⟨v, hv, hve⟩ := h₂; cases hve; exact ⟨k, hv⟩)
          | (obtain ⟨v, hv, hve⟩ := h₃; cases hve; exact ⟨k, hv⟩)

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : HostSemantics H)

/-- **The `$hostcall` premise goes to the erased side**, at an injective naming, a finite host
and an export-blind host. -/
theorem hostPrem_fwd (hinj : Function.Injective hn) (hf : HostFinite host)
    (hb : HostExportBlind host) {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e₀ : Exp}
    {prems : List Prem} (hx : Round8.NxStep.stepRel x = true)
    (hrel : (NxPrims.envBI P hn host).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e₀ prems)) {σ : List (IL.Id × Value)}
    (hq : QuantsOk (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) qs)
    {pat e₁ e₃ : Exp} {z : IL.Id} (hpat : closedOk qs pat = true) (h₁ : closedOk qs e₁ = true)
    (h₃ : closedOk qs e₃ = true) (hz : Param.expP z (.varT "store" []) ∈ qs)
    (h : EvalExp (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ)
      (.memE pat (.callE "hostcall" [.expA e₁, .expA (.varE z), .expA e₃])) (.bool true)) :
    EvalExp (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ))
      (.memE pat (.callE "hostcall" [.expA e₁, .expA (.varE z), .expA e₃])) (.bool true) := by
  obtain ⟨v, ws, l, hv, hws, hc, hm⟩ := (EraseDer.evalExp_hostMem_iff P hn host rfl).1 h
  obtain ⟨h₀, s₀, vs₀, os, rfl, hos, hl⟩ := EraseDer.hostcallCall_inv hc
  obtain rfl := Value.list.inj hl
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hm
  obtain ⟨ha₁, ha₂, ha₃⟩ := evalArgs3_inv hws
  have hr := Round8.NxStep.reach_stepRel hx
  -- the erased arguments
  have ha₂' : EvalExp (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ)) (.varE z)
      (eraseV (storeV hn s₀)) := by
    refine evalExp_varE_iff.2 ?_
    rw [Erase.find?_eraseScope, evalExp_varE_iff.1 ha₂]
    rfl
  have hws' : EvalArgs (NxPrims.envBI P hn host) (eraseScope (VarEnv.empty.bindVals σ))
      [.expA e₁, .expA (.varE z), .expA e₃]
      (Prims.hostArgs hn h₀ (stripStore s₀) vs₀) := by
    rw [← Swap.eraseA_hostArgs]
    exact Equiv.evalArgs_cons (closed_fwd P hn host hx hrel hrule hq h₁ ha₁)
      (Equiv.evalArgs_cons ha₂' (Equiv.evalArgs_cons (closed_fwd P hn host hx hrel hrule hq h₃ ha₃)
        Equiv.evalArgs_nil))
  -- the stripped store has one preimage
  have hq' := Round8.NxTyp.typFwdN_utf8Env hr hrel hrule hq
  obtain ⟨wz, hwz, htz⟩ := hq' _ _ hz
  rw [evalExp_varE_iff.1 ha₂'] at hwz
  obtain rfl := (Option.some.inj hwz).symm
  rw [Swap.eraseV_storeV, EraseDer.mapStore_stripModule, Round8.NxDer.eraseScope_inst] at htz
  have hu' := EraseDer.storeV_uniq_typed P hinj htz (ExpEnc.storeNE_stripStore s₀)
  obtain ⟨os', hos', hcall'⟩ := Swap.hostcallCall_at hn hinj hf (h := h₀) (vs := vs₀) hu'
  refine (EraseDer.evalExp_hostMem_iff P hn host (by rw [Round8.NxDer.eraseScope_inst]; rfl)).2
    ⟨_, _, _, closed_fwd P hn host hx hrel hrule hq hpat hv, hws', hcall', ?_⟩
  rw [Swap.eraseV_outcomeV]
  exact List.mem_map_of_mem ((hos' _).1 (hb.1 h₀ s₀ vs₀ o ((hos o).2 ho)))

/-! ## The rules -/

/-- **`call_ref-hostfunc-res` and `call_ref-hostfunc-div` go to the erased side** at round 4's
primitives, for an injective naming and a finite, export-blind host. -/
theorem ruleFwd_host (hinj : Function.Injective hn) (hf : HostFinite host)
    (hb : HostExportBlind host) {nm : IL.Id} (hnm : nm ∈ hostNamesN) :
    RuleFwdNm (NxPrims.envBI P hn host) nm := by
  intro x op args i v ps t rules qs e e' prems ρ₀ σ hx hrel hrule halt hps hq he hp
  have hB := NxPrims.builtinsVT_BI P hn host
  have H := NxClause.biErase_QT_BI P hn host
  have hF := hostFactsN hx hrel hrule hnm
  obtain ⟨ps₃, pat, e₁, z, e₃, rfl, hps₃, hpat, h₁, h₃, hz⟩ := hF.shape
  refine ruleFwdX hB H hx hrel hrule halt hps hq (fun hρ => ?_) (fun pr hpr _ => hp pr hpr)
    (fun pr hpr hN hρ _ => ?_)
  · subst hρ
    exact concl_fwd hB H hx hrel hrule halt hq (hF.alts e' halt) he
  · subst hρ
    rcases List.mem_append.1 hpr with hpr' | hpr'
    · exact absurd (hps₃ pr hpr') (by simp [hN])
    obtain rfl := List.mem_singleton.1 hpr'
    cases hp _ hpr with
    | ifPr h =>
      exact .ifPr (hostPrem_fwd P hn host hinj hf hb hx hrel hrule hq hpat h₁ h₃ hz h)

end Silmaril.Wasm.SpecTec.Sim.Round9.BadRules
