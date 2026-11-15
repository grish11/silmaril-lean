module

public import Silmaril.Proofs.Wasm.Interp.Invoke
public import Silmaril.Proofs.Wasm.Interp.Div
public import Silmaril.Proofs.Wasm.Interp.Termination
public import Silmaril.Wasm.Binaryen.AdequacyModule

@[expose] public section

/-!
# Store-level native adequacy (proofs)

The native interpreter's final store is the Core 3.0 final store. The forward
simulation `fwd_invoke` already reaches Core configurations whose store is the
interpreter's; `fwd_invoke_store` keeps that in the statement. Backward: by
determinism (`steps_det_nf`), any Core run of an invocation to a result is
that configuration, so its store is the interpreter's.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H} {a : Nat}
  {vs : List Val}

/-- Forward simulation of a native invocation, with the final store. -/
theorem fwd_invoke_store {fuel : Nat} {fl : Binaryen.Flow} (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) (h : Binaryen.invokeRun fuel s a vs = some (s', fl)) :
    ∃ (c : Config H) (r : Result), Steps P host (invoke s a vs) c ∧ c.code = r.toAdmin ∧
      c.store = s' ∧ Binaryen.flowBeh fl = some r.toBehaviour := by
  obtain ⟨fi, fn, ps, rs, F', flb, hfi, hcode, hty, hrun, hfl⟩ := invokeRun_inv h
  obtain ⟨c', o, ob, hst, he, hm, hok', hob⟩ :=
    invoke_body (P := P) (host := host) hS hok hfi hcode hty hrun
  rcases hfl with ⟨ws, hvs, rfl⟩ | ⟨rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · have hnorm : ∀ w, flb = .normal w → w.length = rs.length := by
      rintro w rfl
      exact length_of_ends hok' hob
    obtain ⟨s'', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := ({} : Frame)) he
      (funcPost_of_match (s₂ := s') (F := F') hm hvs (retVals_length hok' hob hvs) hnorm)
    obtain ⟨rfl, rfl⟩ := hK
    exact ⟨_, .values _, hst.trans hret, rfl, rfl, rfl⟩
  · exact ⟨_, .trap, hst.trans (frame_trap he hm), rfl, rfl, rfl⟩
  · rcases o <;> simp only [FlowMatch] at hm

/-- Backward simulation with the final store, at the closed deterministic
profile. -/
theorem bwd_store_det {o : GrowKind → Nat → Nat → Nat → Bool} {c : Config H} {r : Result}
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (div : Binaryen.DivSim (Profile.deterministic o) s a vs)
    (sn : Binaryen.NoDivOfTerm (Profile.deterministic o) s a vs)
    (hst : Steps (Profile.deterministic o) Binaryen.closedHost (invoke s a vs) c)
    (hc : c.code = r.toAdmin) :
    ∃ fuel fl, Binaryen.invokeRun fuel s a vs = some (c.store, fl) ∧
      Binaryen.flowBeh fl = some r.toBehaviour := by
  by_cases hex : ∃ fuel s' fl, Binaryen.invokeRun fuel s a vs = some (s', fl)
  · obtain ⟨fuel, s', fl, hrun⟩ := hex
    obtain ⟨c₂, r₂, hst₂, hc₂, hs₂, hb⟩ :=
      fwd_invoke_store (P := Profile.deterministic o) (host := Binaryen.closedHost) hS hok hrun
    obtain rfl := Binaryen.steps_det_nf hst hst₂ (fun _ => Binaryen.not_step_terminal' ⟨r, hc⟩)
      (fun _ => Binaryen.not_step_terminal' ⟨r₂, hc₂⟩)
    obtain rfl := Binaryen.result_toAdmin_inj (hc.symm.trans hc₂)
    exact ⟨fuel, fl, hs₂ ▸ hrun, hb⟩
  · have hnone : ∀ fuel, Binaryen.invokeRun fuel s a vs = none := by
      intro fuel
      rcases h : Binaryen.invokeRun fuel s a vs with _ | ⟨s', fl⟩
      · rfl
      · exact absurd ⟨fuel, s', fl, h⟩ hex
    exact absurd (div hnone) (sn ⟨c, hst, r, hc⟩)

/-- **Backward simulation with the final store, at every profile**, on typed,
native, arity-checked stores. -/
theorem bwd_store (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) {c : Config H} {r : Result}
    (hst : Steps P Binaryen.closedHost (invoke s a vs) c) (hc : c.code = r.toAdmin) :
    ∃ fuel fl, Binaryen.invokeRun fuel s a vs = some (c.store, fl) ∧
      Binaryen.flowBeh fl = some r.toBehaviour := by
  let D : Profile := Profile.deterministic fun _ _ _ _ => false
  have hcfg : NConfig (invoke s a vs) := nConfig_invoke hF a vs
  have hst' : Steps D Binaryen.closedHost (invoke s a vs) c := (steps_profile_iff hcfg).mp hst
  exact bwd_store_det hS hok (divSim_native hs hF hS hok) (noDivOfTerm_native hs hF hok) hst' hc

end Silmaril.Wasm.Interp
