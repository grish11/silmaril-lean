module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Abstract.Recursion.Basic

/-!
# Closing against Core 3.0: proofs

The native interpreter's runs of an invocation are the closed outcomes, so by
(store-level) native adequacy the Core 3.0 behaviours and final stores of a
native invocation are the closed outcomes, with divergence exactly when there
is none.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Recursion

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem invokeRun_some_iff {s : Store H} {a : Nat} {vs : List Val} {s' : Store H} {fl : Flow} :
    (∃ fuel, invokeRun fuel s a vs = some (s', fl)) ↔ ClosedOutcome s a vs s' fl := by
  constructor
  · rintro ⟨fuel, h⟩
    unfold invokeRun at h
    rcases hfi : s.funcs[a]? with _ | fi
    · simp [hfi] at h
    · simp only [hfi] at h
      rcases hc : fi.code with fn | hh
      · rcases ht : Validation.DefType.funcType? fi.type with _ | ⟨ps, rs⟩
        · simp [hc, ht] at h
        · simp only [hc, ht] at h
          rcases hr : run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) with
            _ | ⟨s₁, f₁, bfl⟩
          · simp [hr] at h
          · rw [hr] at h
            have he := eval_of_run hr
            have hss : s₁ = s' := by
              rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | x <;> simp_all
            subst hss
            refine ⟨fi, fn, ps, rs, f₁, bfl, hfi, hc, ht, evalO_closed_iff.mpr he, ?_⟩
            rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | x <;> simp_all [exitFlow]
      · simp [hc] at h
  · rintro ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, ht, he, hx⟩
    obtain ⟨fuel, hr⟩ := run_of_eval (evalO_closed_iff.mp he)
    refine ⟨fuel, ?_⟩
    unfold invokeRun
    simp only [hfi, hc, ht, hr]
    rcases bfl with ws | ⟨_ | k, ws⟩ | ws | _ | x <;> simp_all [exitFlow]

/-- Core 3.0 runs of a native invocation to a result, final store included,
are the closed outcomes. -/
theorem core_result_iff_closed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) (r : Result) (s' : Store H) :
    (∃ c : Config H, Steps P closedHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧ c.store = s') ↔
      ∃ fl, ClosedOutcome s a vs s' fl ∧ flowBeh fl = some r.toBehaviour := by
  rw [Silmaril.Wasm.Interp.native_store_adequacy hs hF hS hok P r s']
  constructor
  · rintro ⟨fuel, fl, hr, hb⟩
    exact ⟨fl, invokeRun_some_iff.mp ⟨fuel, hr⟩, hb⟩
  · rintro ⟨fl, hc, hb⟩
    obtain ⟨fuel, hr⟩ := invokeRun_some_iff.mpr hc
    exact ⟨fuel, fl, hr, hb⟩

/-- The Core 3.0 behaviours of a native invocation are its closed outcomes, and
divergence exactly when it has none. -/
theorem behaviours_eq_closed {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    behaviours P closedHost s a vs =
      {b | (∃ s' fl, ClosedOutcome s a vs s' fl ∧ flowBeh fl = some b) ∨
        (b = .diverges ∧ ∀ s' fl, ¬ ClosedOutcome s a vs s' fl)} := by
  rw [Silmaril.Wasm.Interp.native_adequacy hs hF hS hok]
  ext b
  constructor
  · rintro (⟨fuel, s', fl, hr, hb⟩ | ⟨rfl, hd⟩)
    · exact .inl ⟨s', fl, invokeRun_some_iff.mp ⟨fuel, hr⟩, hb⟩
    · refine .inr ⟨rfl, fun s' fl hc => ?_⟩
      obtain ⟨fuel, hr⟩ := invokeRun_some_iff.mpr hc
      rw [hd fuel] at hr
      cases hr
  · rintro (⟨s', fl, hc, hb⟩ | ⟨rfl, hd⟩)
    · obtain ⟨fuel, hr⟩ := invokeRun_some_iff.mpr hc
      exact .inl ⟨fuel, s', fl, hr, hb⟩
    · refine .inr ⟨rfl, fun fuel => ?_⟩
      rcases h : invokeRun fuel s a vs with _ | ⟨s', fl⟩
      · rfl
      · exact absurd (invokeRun_some_iff.mp ⟨fuel, h⟩) (hd s' fl)

end Silmaril.Proofs.Wasm.Abstract.Recursion
