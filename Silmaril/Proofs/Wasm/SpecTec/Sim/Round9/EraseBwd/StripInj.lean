module

public import Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.BadRules.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Thms

/-!
# The backward and export leaves on `StripInj` configurations

At a `StripInj` configuration `c` and an export-blind host that is export-parametric or invents no
module:

* `eraseBwdAt_param`, `eraseBwdAt_modsSub`: a step of round 6 from `configV hn (stripConfig c)`
  goes to `configV hn d₀` with `d₀` export-free (round 6's backward half and
  `Round7.stripped_step`); round 7's export swap lifts it to a step from `configV hn c` to
  `configV hn (mapConfig (unstrip c) d₀)`, whose erasure is `configV hn d₀`.
* `exactAt_param`: the export leaf, by `Round7.bwdREI_of_leaves`; `CoreStrip.exactAt_of_REM` is
  the module-preserving case.
* `leavesBwdAt_stripInj`, `leavesREHBwd_of_out`, `leavesREHBwd_iff_out`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7
open Round9.CoreStrip
open Round4Int (BI)

variable {H : Type}

/-! ## The leaves on `StripInj` configurations -/

/-- The erasure of the image of `mapConfig (unstrip c) d₀`, for an export-free `d₀`. -/
theorem eraseV_unstrip (hn : H → String) (c d₀ : Config H) (hstr : Stripped d₀) :
    Swap.eraseV (configV hn (mapConfig (unstrip c) d₀)) = configV hn d₀ := by
  rw [Swap.eraseV_configV, Runs.stripConfig_mapConfig (exportOnly_unstrip c), hstr]

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host) {nd : Bool}
  {r : RelaxedChoice}
include hinj hf hh hb

/-- A step of round 6 from the stripped image goes to the image of an export-free `d₀`, and is a
step of the round-7 reading. -/
theorem stripped_succ (c : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) {w₀ : Value}
    (hw₀ : Round6.Int.backend.step (BI (Profile.spec nd r) hn host)
      (configV hn (stripConfig c)) w₀) :
    ∃ d₀ : Config H, Stripped d₀ ∧ w₀ = configV hn d₀ ∧
      Round6.Reading.SStepB (utf8Env (BI (Profile.spec nd r) hn host))
        (configV hn (stripConfig c)) (configV hn d₀) := by
  obtain ⟨c₀, d₀, hd, rfl, hst⟩ :=
    Round6.Target.bwdR_of_open hinj hf (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf hh) (stripConfig c) ts _
      (configOk_strip hc) (boundedSel_strip hbc) hw₀
  have hstr : Stripped d₀ := stripped_of_configEq hd (stripped_step hb hst (stripped_stripConfig c))
  exact ⟨d₀, hstr, rfl, (Runs.agree_strip hb (Profile.spec nd r) c _).mpr hw₀⟩

/-- **The backward leaf at a `StripInj` configuration, for an export-parametric host.** -/
theorem eraseBwdAt_param (hp : HostExportParam host) (c : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hbc : BoundedSelE c) (hic : StripInj c) :
    EraseBwdAt hn (Profile.spec nd r) host c := by
  rw [EraseBwdAt, stripHostAt_of_blind hb]
  intro w₀ hw₀
  obtain ⟨d₀, hstr, rfl, h₁⟩ := stripped_succ hinj hf hh hb c ts hc hbc hw₀
  exact ⟨_, (EraseDer.swapEquiv_holds H hn hinj host hf hh hb hp nd r c ts hc hbc hic).1 d₀ hstr h₁,
    eraseV_unstrip hn c d₀ hstr⟩

/-- **The backward leaf at a `StripInj` configuration, for a host that invents no module.** -/
theorem eraseBwdAt_modsSub (hm : HostMods.HostModsSub host) (c : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hbc : BoundedSelE c) (hic : StripInj c) :
    EraseBwdAt hn (Profile.spec nd r) host c := by
  rw [EraseBwdAt, stripHostAt_of_blind hb]
  intro w₀ hw₀
  obtain ⟨d₀, hstr, rfl, h₁⟩ := stripped_succ hinj hf hh hb c ts hc hbc hw₀
  exact ⟨_, HostMods.swapAt_fwdM hinj hf hb hm _ hic hbc.2 (fun _ h => h) hstr h₁,
    eraseV_unstrip hn c d₀ hstr⟩

/-- **The export leaf at a `StripInj` configuration, for an export-parametric host.** -/
theorem exactAt_param (hp : HostExportParam host) (c : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hbc : BoundedSelE c) (hic : StripInj c) :
    ExactAt hn (Profile.spec nd r) host c :=
  fun _ w _ hw _ =>
    bwdREI_of_leaves EraseDer.swapEquiv_holds Determ.envAgreeNE hinj hf hh hb hp c ts w hc hbc
      hic hw

/-- **Both remaining leaves on `StripInj` configurations**, for an export-blind host that is
export-parametric or invents no module. -/
theorem leavesBwdAt_stripInj (hpm : HostExportParam host ∨ HostMods.HostModsSub host)
    (c : Config H) (ts : List CValType) (hc : ConfigOk c ts) (hbc : BoundedSelE c)
    (hic : StripInj c) :
    EraseBwdAt hn (Profile.spec nd r) host c ∧ ExactAt hn (Profile.spec nd r) host c := by
  rcases hpm with hp | hm
  · exact ⟨eraseBwdAt_param hinj hf hh hb hp c ts hc hbc hic,
      exactAt_param hinj hf hh hb hp c ts hc hbc hic⟩
  · exact ⟨eraseBwdAt_modsSub hinj hf hh hb hm c ts hc hbc hic,
      exactAt_of_REM hinj hf hh hb hm c ts hc hbc hic⟩

end

/-- **`LeavesREHBwd` from its open part**: the proved case covers the rest. -/
theorem leavesREHBwd_of_out (h : LeavesREHBwdOut) : BadRules.LeavesREHBwd := by
  intro H hn hinj host hf hh hb nd r c ts hc hbc
  by_cases hd : StripInj c ∧ (HostExportParam host ∨ HostMods.HostModsSub host)
  · exact leavesBwdAt_stripInj hinj hf hh hb hd.2 c ts hc hbc hd.1
  · exact h H hn hinj host hf hh hb nd r c ts hc hbc hd

/-- `LeavesREHBwdOut` is `LeavesREHBwd`, restricted. -/
theorem leavesREHBwd_iff_out : BadRules.LeavesREHBwd ↔ LeavesREHBwdOut :=
  ⟨fun h H hn hinj host hf hh hb nd r c ts hc hbc _ => h H hn hinj host hf hh hb nd r c ts hc hbc,
    leavesREHBwd_of_out⟩

/-- **`Round7.Task.wholeStepValidREH` from `LeavesREHBwdOut`.** -/
theorem wholeStepValidREH_of_out (h : LeavesREHBwdOut) : Round7.Task.wholeStepValidREH :=
  BadRules.wholeStepValidREH_of_bwd (leavesREHBwd_of_out h)

end Silmaril.Wasm.SpecTec.Sim.Round9.EraseBwd
