module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Widen
public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Approx
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

@[expose] public section

/-!
# Typing in context, transferred (proofs)

`Sim.ContextTyped` types a configuration at the hole of a typed whole configuration. Both transfers
of this topic lift to it: code equal up to existing exception addresses (`contextTyped_approx`),
and a widened store that is `StoreOk` (`contextTyped_widen`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (ActiveCtx ContextTyped)

variable {H : Type}

theorem plug_store (E : ActiveCtx) : ∀ (c : Config H), (E.plug c).store = c.store := by
  induction E with
  | hole => intro c; rfl
  | suffix rest E ih => intro c; exact ih _
  | label n cont vs rest E ih => intro c; exact ih _
  | handler n cs vs rest E ih => intro c; exact ih _
  | frame n f vs rest E ih => intro c; exact ih _

/-- Plugging does not read the store except to keep it. -/
theorem plug_mk (E : ActiveCtx) : ∀ (s t : Store H) (f : Frame) (es : List Admin),
    E.plug ⟨t, f, es⟩ = ⟨t, (E.plug ⟨s, f, es⟩).frame, (E.plug ⟨s, f, es⟩).code⟩ := by
  induction E with
  | hole => intro s t f es; rfl
  | suffix rest E ih => intro s t f es; exact ih s t f _
  | label n cont vs rest E ih => intro s t f es; exact ih s t f _
  | handler n cs vs rest E ih => intro s t f es; exact ih s t f _
  | frame n f₀ vs rest E ih => intro s t f es; exact ih s t f₀ _

theorem plug_approx {N : Nat} (E : ActiveCtx) : ∀ {s : Store H} {f : Frame} {es es' : List Admin},
    CodeApprox N es es' → (E.plug ⟨s, f, es⟩).frame = (E.plug ⟨s, f, es'⟩).frame ∧
      CodeApprox N (E.plug ⟨s, f, es⟩).code (E.plug ⟨s, f, es'⟩).code := by
  induction E with
  | hole => intro s f es es' h; exact ⟨rfl, h⟩
  | suffix rest E ih => intro s f es es' h; exact ih (h.append (.refl _))
  | label n cont vs rest E ih =>
    intro s f es es' h
    exact ih (((CodeApprox.refl _).append (.cons (.label _ _ h) .nil)).append (.refl _))
  | handler n cs vs rest E ih =>
    intro s f es es' h
    exact ih (((CodeApprox.refl _).append (.cons (.handler _ _ h) .nil)).append (.refl _))
  | frame n f₀ vs rest E ih =>
    intro s f es es' h
    exact ih (((CodeApprox.refl _).append (.cons (.frame _ _ h) .nil)).append (.refl _))

/-- **Typing in context transfers to code equal up to existing exception addresses.** -/
theorem contextTyped_approx {s : Store H} {f : Frame} {es es' : List Admin}
    (h : ContextTyped ⟨s, f, es'⟩) (hx : CodeApprox s.exns.length es es') :
    ContextTyped ⟨s, f, es⟩ := by
  obtain ⟨E, ts, C, hst, ha⟩ := h
  obtain ⟨hfr, hc⟩ := plug_approx (s := s) (f := f) E hx
  refine ⟨E, ts, C, ?_, ?_⟩
  · rw [plug_store, hfr]; rw [plug_store] at hst; exact hst
  · rw [plug_store]; rw [plug_store] at ha
    exact adminsOk_approx ha hc

/-- **Typing in context transfers to a widened store that is `StoreOk`.** -/
theorem contextTyped_widen {s t : Store H} {f : Frame} {es : List Admin} (hw : Widen s t)
    (ht : StoreOk t) (h : ContextTyped ⟨s, f, es⟩) : ContextTyped ⟨t, f, es⟩ := by
  obtain ⟨E, ts, C, ⟨-, hfr⟩, ha⟩ := h
  refine ⟨E, ts, C, ?_, ?_⟩
  · rw [plug_mk E s t]; rw [plug_store] at hfr
    exact ⟨ht, hw.frameOk hfr⟩
  · rw [plug_mk E s t]; rw [plug_store] at ha
    exact hw.adminsOk ha

/-- The store of a configuration typed in context is `StoreOk`. -/
theorem storeOk_of_contextTyped {c : Config H} (h : ContextTyped c) : StoreOk c.store := by
  obtain ⟨E, ts, C, ⟨hs, -⟩, -⟩ := h
  rwa [plug_store] at hs

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
