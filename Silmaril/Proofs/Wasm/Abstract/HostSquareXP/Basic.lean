module

public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.HostSquare.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms

/-!
# The exact-log commuting square for the canonical closure (proofs)

Case by case from the exact-log pieces of `Silmaril.Wasm.Abstract.HostClosingXP` (deterministic
profile, the hypotheses of its backward lemmas):

* `square_done`: `wasmEvFunXP_vals_iff`, `wasmEvFunXP_throw_iff`, `wasmEvFunXP_trap_iff`; `div` is
  no closed behaviour (`wasmEvFunXP_ne_div`) and no Core end;
* `square_blocked`, `square_hostDiv`: `wasmEvPendXP_evRun_iff`, with the host filters read by
  `coreHostRel_noAns_iff`;
* `square_div_of`, `square_prod_of`, `square_of`: the remaining two cases from the forward
  theorems of `Silmaril.Wasm.Abstract.HostClosingInfXP` and the converse directions, taken as
  explicit hypotheses.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostSquareXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp (HostSliceT HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {a : Nat} {vs : List Val}

section Back

variable (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
  (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
  (hok : InvokeOk s a vs)
include hT hH hE hs hS hts hok

/-- **Finished ends.** -/
theorem square_done (cs : List (Call (wasmHostSig H))) (e : End (Store H) (List Val ⊕ Nat)) :
    NatObsXP host s a vs (.done cs e) ↔ CoreObsLXP (profile o) host s a vs (.done cs e) := by
  rcases e with ⟨ws | t, s₂⟩ | _ | _
  · exact wasmEvFunXP_vals_iff hT hH hE hs hS hts hok
  · exact wasmEvFunXP_throw_iff hT hH hE hs hS hts hok
  · exact wasmEvFunXP_trap_iff hT hH hE hs hS hts hok
  · exact ⟨fun h => wasmEvFunXP_ne_div h.1, fun h => h.elim⟩

/-- **Pending calls with no host outcome.** -/
theorem square_blocked (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op) :
    NatObsXP host s a vs (.blocked cs m) ↔ CoreObsLXP (profile o) host s a vs (.blocked cs m) := by
  obtain ⟨hh, s', us⟩ := m
  have hp := wasmEvPendXP_evRun_iff (o := o) (hh := hh) (s' := s') (us := us) (cs := cs)
    hT hH hE hs hS hts hok
  constructor
  · rintro ⟨h, hc, hno⟩
    obtain ⟨c, E, a', hrun, hd, hst⟩ := hp.mp ⟨h, hc⟩
    exact ⟨c, E, a', hrun, hd, hst, coreHostRel_noAns_iff.mp hno⟩
  · rintro ⟨c, E, a', hrun, hd, hst, hno⟩
    obtain ⟨h, hc⟩ := hp.mpr ⟨c, E, a', hrun, hd, hst⟩
    exact ⟨h, hc, coreHostRel_noAns_iff.mpr hno⟩

/-- **Pending calls the host diverges on.** -/
theorem square_hostDiv (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op) :
    NatObsXP host s a vs (.hostDiv cs m) ↔ CoreObsLXP (profile o) host s a vs (.hostDiv cs m) := by
  obtain ⟨hh, s', us⟩ := m
  have hp := wasmEvPendXP_evRun_iff (o := o) (hh := hh) (s' := s') (us := us) (cs := cs)
    hT hH hE hs hS hts hok
  constructor
  · rintro ⟨h, hc, hdiv⟩
    obtain ⟨c, E, a', hrun, hd, hst⟩ := hp.mp ⟨h, hc⟩
    exact ⟨c, E, a', hrun, hd, hst, hdiv⟩
  · rintro ⟨c, E, a', hrun, hd, hst, hdiv⟩
    obtain ⟨h, hc⟩ := hp.mpr ⟨c, E, a', hrun, hd, hst⟩
    exact ⟨h, hc, hdiv⟩

end Back

section Of

variable (hH : HostSliceT host) (hE : HostSliceE tags host)
  (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
include hH hE hS hts hok

/-- **Divergence after a log**, from the converse direction as a hypothesis. -/
theorem square_div_of
    (hdiv : ∀ (cs : List (Call (wasmHostSig H))) (c' : Config H),
      EvRun (profile o) host (invoke s a vs) cs c' →
      Diverges (profile o) (fun _ _ _ _ => False) c' → (cs, .div) ∈ wasmEvFunDXP s (a, vs))
    (cs : List (Call (wasmHostSig H))) :
    NatObsXP host s a vs (.div cs) ↔ CoreObsLXP (profile o) host s a vs (.div cs) :=
  ⟨fun h => wasmEvFunDXP_div_evRun hH hE hts hS hok h.1 h.2,
    fun ⟨c', hrun, hd⟩ => ⟨hdiv cs c' hrun hd, evRun_consistent hrun⟩⟩

/-- **Productive runs**, from the converse direction as a hypothesis. -/
theorem square_prod_of
    (hinf : ∀ ω : Nat → Call (wasmHostSig H), CoreInf (profile o) host (invoke s a vs) ω →
      ω ∈ wasmEvInfNXP s (a, vs))
    (ω : Nat → Call (wasmHostSig H)) :
    NatObsXP host s a vs (.prod ω) ↔ CoreObsLXP (profile o) host s a vs (.prod ω) :=
  ⟨fun h => hostObsInf_wasmEvInfNXP_coreInf hH hE hts hS hok h,
    fun h => ⟨hinf ω h, fun n => coreInf_consistent h n⟩⟩

end Of

/-- **The square, from the two converse directions as hypotheses.** -/
theorem square_of (hT : HostTyped host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs)
    (hdiv : ∀ (cs : List (Call (wasmHostSig H))) (c' : Config H),
      EvRun (profile o) host (invoke s a vs) cs c' →
      Diverges (profile o) (fun _ _ _ _ => False) c' → (cs, .div) ∈ wasmEvFunDXP s (a, vs))
    (hinf : ∀ ω : Nat → Call (wasmHostSig H), CoreInf (profile o) host (invoke s a vs) ω →
      ω ∈ wasmEvInfNXP s (a, vs))
    (x : FullObs H) : NatObsXP host s a vs x ↔ CoreObsLXP (profile o) host s a vs x := by
  cases x with
  | done cs e => exact square_done hT hH hE hs hS hts hok cs e
  | blocked cs m => exact square_blocked hT hH hE hs hS hts hok cs m
  | hostDiv cs m => exact square_hostDiv hT hH hE hs hS hts hok cs m
  | div cs => exact square_div_of hH hE hS hts hok hdiv cs
  | prod ω => exact square_prod_of hH hE hS hts hok hinf ω

end Silmaril.Proofs.Wasm.Abstract.HostSquareXP
