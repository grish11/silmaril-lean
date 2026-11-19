module

public import Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Thms

/-!
# Round 9, REH: the backward lift by induction on the erased derivation

* `dderivesB_lift`: `RuleLift` at every rule of the `liftRel` relations gives `LiftV` at every
  derivation of them (mutual structural induction with `dpremB_lift`, which attaches the lift to
  the relation premises).
* `eraseBwdAt_of_lift`: at an export-blind host, `CoreStrip.EraseBwdAt hn P host c` from
  `RuleLift` at every rule of the round-7 environment and the provenance of `configV hn c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB DPremB conclAlts)

section

set_option linter.unusedSectionVars false

variable {env : Env} {O : ElseI} {Prov : IL.Id → Value → Prop}
  (hR : ∀ x i, liftRel x = true → RuleLift env O Prov x i)
include hR

mutual
/-- **The backward lift of a derivation**, from `RuleLift` at every rule. -/
theorem dderivesB_lift :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesB env O x op args v → liftRel x = true → LiftV env O Prov x op args v
  | x, _, _, _, .rule (i := i) hrel hrule halt hps hq he hp, hx =>
    hR x i hx hrel hrule halt hps hq he fun pr hpr => dpremB_lift (hp pr hpr)
termination_by structural _ _ _ _ hd => hd

/-- A premise of a derivation, with the lift at its `liftRel` relation premises. -/
theorem dpremB_lift :
    ∀ {els : Prop} {ρ : VarEnv} {pr : Prem}, DPremB env O els ρ pr → DPremL env O Prov els ρ pr
  | _, _, _, .ifPr h => .ifPr h
  | _, _, _, .elsePr h => .elsePr h
  | _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, _, .rulePr ha he hd => .rulePr ha he hd fun hx => dderivesB_lift hd hx
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremB_lift hp)
  | _, _, _, .iterList hit hd hne hl hk hp =>
    .iterList hit hd hne hl hk fun r hr => dpremB_lift (hp r hr)
  | _, _, _, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => dpremB_lift (hp r hr)
termination_by structural _ _ _ hd => hd
end

end

/-- **The backward SpecTec leaf from the rule lifts**, at an export-blind host: `RuleLift` at
every rule of `Step`, `Step_read` and `Step_pure` in the round-7 environment, read with SpecTec's
`otherwise`, and the provenance of the original image `configV hn c`. -/
theorem eraseBwdAt_of_lift {H : Type} {hn : H → String}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} (hb : HostExportBlind host)
    (P : Silmaril.Wasm.Numerics.Profile) {Prov : IL.Id → Value → Prop}
    (hR : ∀ x i, liftRel x = true →
      RuleLift (utf8Env (Round4Int.BI P hn host))
        (Round6.Reading.otherwiseB (utf8Env (Round4Int.BI P hn host))) Prov x i)
    (c : Silmaril.Wasm.Execution.Core.Config H) (hc : Prov "Step" (configV hn c)) :
    CoreStrip.EraseBwdAt hn P host c := by
  rw [CoreStrip.eraseBwdAt_blind_iff hb]
  intro w₀ hw₀
  have h₁ := (Runs.agree_strip hb P c w₀).mpr hw₀
  rw [← Swap.eraseV_configV] at h₁
  exact dderivesB_lift hR h₁ rfl _ _ rfl hc

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
