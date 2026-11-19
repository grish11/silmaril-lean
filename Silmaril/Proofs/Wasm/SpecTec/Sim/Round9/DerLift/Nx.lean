module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.DerLift.Simple

/-!
# Round 9, REH: the backward lift at the rules with nothing to rebind

`ruleLift_nx`: `RuleLift` at every rule of `Step`, `Step_read` or `Step_pure` that passes
`liftNx`, for every provenance. Every quantifier is export-free, and the left-hand side `L` of
the conclusion is export-free (`NxSites.nxE`, read by `NxRule.eOk_of_closed`). So the erased
input `L(σ₀) = eraseV a` has no export list, and `a = L(σ₀)`: the original input is the erased
one. The erased instance is then itself an instance at `(a, b₀)`, its premises unchanged, and
round 7's equation `NxErase.erase_alt` shows `eraseV b₀ = b₀` (the scope's values are their own
erasures).
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
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {B : Builtins}

/-- Forgetting the lifts of a premise. -/
theorem dpremL_toB {env : Env} {O : ElseI} {Prov : IL.Id → Value → Prop} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremL env O Prov els ρ pr → DPremB env O els ρ pr
  | _, _, .ifPr h => .ifPr h
  | _, _, .elsePr h => .elsePr h
  | _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, .rulePr ha he hd _ => .rulePr ha he hd
  | _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremL_toB hp)
  | _, _, .iterList hit hd hne hl hk hp =>
    .iterList hit hd hne hl hk fun r hr => dpremL_toB (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => dpremL_toB (hp r hr)

theorem liftRel_reach {x : IL.Id} (hx : liftRel x = true) : reach 0 x = true := by
  simp only [liftRel, Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with (rfl | rfl) | rfl <;> decide

section Nx

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **`RuleLift` at the rules that pass `liftNx`**, for every reading of `otherwise` and every
provenance. -/
theorem ruleLift_nx {O : ElseI} {Prov : IL.Id → Value → Prop} {x : IL.Id} (hx : liftRel x = true)
    {i : Nat} (hs : ∀ ps op t rules r, (utf8Env B).findRel? x = some (ps, op, t, rules) →
      rules[i]? = some r → liftNx r = true) :
    RuleLift (utf8Env B) O Prov x i := by
  intro op args v₀ ps t rules nm qs e e' prems ρ₀ σ hrel hrule halt hps hq hev hpr a b₀ hv₀ _
  have hr := liftRel_reach hx
  have hD := NxFlow.flowSound B hB
  have hF := NxRule.rFacts hr hrel hrule
  obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
  subst hρ hargs
  have hsl := hs ps op t rules _ hrel hrule
  simp only [liftNx, Bool.and_eq_true, List.all_eq_true] at hsl
  obtain ⟨hqn, hll⟩ := hsl
  have hll' := hll e' halt
  split at hll'
  case h_2 => cases hll'
  rename_i l r
  simp only [Bool.and_eq_true] at hll'
  obtain ⟨⟨⟨⟨hlc, hlt⟩, hla⟩, hlnx⟩, hxe⟩ := hll'
  -- every quantifier value is export-free
  have hval : ∀ y ty, Param.expP y ty ∈ qs → ∃ w,
      (VarEnv.empty.bindVals σ).findVal? y = some w ∧ nxB w = true := by
    intro y ty hy
    have hnt : Round8.NxTyp.nxT ty = true := by
      simp only [ElseRef.quantsNxL, List.all_eq_true] at hqn
      simpa using hqn _ hy
    exact NxSites.nxB_of_quantsOk (NxSites.typsNx_bindVals (NxSites.typsNx_empty _) σ) hq hy hnt
  have hag : VarEnv.AgreeOn (freeExp (.tupE [l, r])) (eraseScope (VarEnv.empty.bindVals σ))
      (VarEnv.empty.bindVals σ) := by
    refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [Erase.find?_eraseScope]
    obtain ⟨ty, hty⟩ := mem_quantNames (EraseDer.varsIn_mem (hF.alts _ halt).2 y hy)
    obtain ⟨w, hw, hnw⟩ := hval y ty hty
    rw [hw]
    simp [Swap.eraseV_of_nxB _ hnw]
  obtain ⟨n, hn⟩ := hev
  have hE := NxErase.erase_alt hD H hr hrel hrule hq
    (fun k => NxClause.clauseErase B hB H _ k rfl rfl) halt hxe n
  rw [evalExp_agreeOn hag, hn] at hE
  obtain ⟨k, lv, rv, -, hl, -, hw⟩ := Round8.NxElse.evalExp_pair hn
  rw [hw] at hv₀ hE
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv₀
  obtain ⟨hlv, hrv⟩ := hv₀
  -- the left-hand side is export-free, so the original input is the erased one
  have hlnxB : nxB lv = true :=
    NxRule.nxB_of_eOk (NxRule.eOk_of_closed hD hq hF.wild hlc hlt hla ⟨k, hl⟩) hlnx
  have ha : a = eraseV a := eq_of_eraseV_nxB rfl (hlv ▸ hlnxB)
  have hb : eraseV b₀ = b₀ := by
    simp only [Functor.map, Except.map, Except.ok.injEq, eraseV, eraseVs, Value.tuple.injEq,
      List.cons.injEq, and_true] at hE
    rw [← hrv]
    exact hE.2.symm
  have hv : v₀ = .tuple [a, b₀] := by rw [hw, hlv, hrv, ← ha]
  subst hv
  exact ⟨b₀, .rule hrel hrule halt hps hq ⟨n, hn⟩ fun pr hp => dpremL_toB (hpr pr hp), hb⟩

end Nx

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
