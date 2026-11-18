module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Supp
public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Alloc

@[expose] public section

/-!
# The relaxed configuration invariant and its preservation (proofs)

`ConfigOkD c`: the configuration is in the supported profile (`ASupp`, frames below the store's
tags, supported functions), struct and array fields name exceptions of the store (`HeapBelow`),
and some typing witness `gst c.store T X` (`GhostOk`) types its code in context
(`Sim.ContextTyped`). The actual store is never changed: the witness only types.

`ConfigOkD.step`: every host-free Core step (every numeric profile) keeps `ConfigOkD`. A step
that keeps the exceptions is matched on the witness (`step_ghost`), typed there by Core
preservation (`Sim.ContextTyped.step`), and the actual code is typed up to caught payloads
(`contextTyped_approx`). A Wasm `throw` moves to the witness `alloc_ghost`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm.Cfg.DanglingTyped
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (ContextTyped)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

theorem GhostOk.congr {s s' : Store H} {T : List TagInst} {X : List ExnInst}
    (ht : s'.tags = s.tags) (he : s'.exns = s.exns) (h : GhostOk s T X) : GhostOk s' T X := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨ht ▸ h1, he ▸ h2, he ▸ h3, fun a e' ha hx => by rw [he, ht] at *; exact h4 a e' ha hx⟩

theorem HeapBelow.mono {s s' : Store H} (hs : s'.structs = s.structs) (ha : s'.arrays = s.arrays)
    (he : s.exns.length ≤ s'.exns.length) (h : HeapBelow s) : HeapBelow s' := by
  refine ⟨fun si hsi r hr => ?_, fun ai hai r hr => ?_⟩
  · rw [hs] at hsi
    exact RefLeaves.mono (fun a h => Nat.lt_of_lt_of_le h he) (h.1 si hsi r hr)
  · rw [ha] at hai
    exact RefLeaves.mono (fun a h => Nat.lt_of_lt_of_le h he) (h.2 ai hai r hr)

/-- A supported host-free step keeps structs and arrays and does not shrink the exceptions. -/
theorem step_heap {k : Nat} {c c' : Config H} (h : Step P NH c c') (hs : ∀ a ∈ c.code, ASupp k a) :
    c'.store.structs = c.store.structs ∧ c'.store.arrays = c.store.arrays ∧
      c.store.exns.length ≤ c'.store.exns.length := by
  induction h with
  | «variable» hp => cases hp <;> exact ⟨rfl, rfl, Nat.le_refl _⟩
  | table hp => cases hp <;> exact ⟨rfl, rfl, Nat.le_refl _⟩
  | memory hp => cases hp <;> exact ⟨rfl, rfl, Nat.le_refl _⟩
  | reference hp => cases hp <;> exact ⟨rfl, rfl, Nat.le_refl _⟩
  | aggregate hp => exact (AggregateStep.not_supp hp hs).elim
  | ctxtInstrs _ _ ih => exact ih fun a ha => hs a (by simp [ha])
  | ctxtLabel _ ih => exact ih (asupp_label_inv (hs _ (List.mem_singleton_self _))).2
  | ctxtHandler _ ih => exact ih (asupp_handler_inv (hs _ (List.mem_singleton_self _)))
  | ctxtFrame _ ih => exact ih (asupp_frame_inv (hs _ (List.mem_singleton_self _))).2
  | throw _ _ _ => exact ⟨rfl, rfl, by simp [Store.addExn]⟩
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | _ => exact ⟨rfl, rfl, Nat.le_refl _⟩

/-- **Preservation of the relaxed invariant by a host-free Core step.** -/
theorem ConfigOkD.step {c c' : Config H} (hc : ConfigOkD c) (h : Step P NH c c') :
    ConfigOkD c' := by
  obtain ⟨hF, hf, hs, hheap, T, X, hg, hct⟩ := hc
  obtain ⟨ht, hfn, hf', hs'⟩ := step_supp h hF hf hs
  obtain ⟨hst, har, hle⟩ := step_heap h hs
  refine ⟨?_, ht ▸ hf', ht ▸ hs', HeapBelow.mono hst har hle hheap, ?_⟩
  · intro fi hfi
    rw [hfn] at hfi
    rw [ht]
    exact hF fi hfi
  · rcases step_ghost h hg hf hs with ⟨ht', he', es, hgst, hx⟩ | ⟨e, he, es, hgst, hx⟩
    · exact ⟨T, X, GhostOk.congr ht' he' hg, contextTyped_approx (hct.step hgst) hx⟩
    · have hct' := hct.step hgst
      obtain ⟨c'₀, f', code'⟩ := c'
      dsimp only at he hct' hx ⊢
      subst he
      obtain ⟨X', hlen, hg', hct''⟩ := alloc_ghost hg hheap hct'
      refine ⟨T, X', hg', contextTyped_approx hct'' ?_⟩
      show CodeApprox X'.length _ _
      rw [hlen]; exact hx

/-- **Preservation along host-free runs.** -/
theorem ConfigOkD.steps {c c' : Config H} (hc : ConfigOkD c) (h : Steps P NH c c') :
    ConfigOkD c' := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact ConfigOkD.step ih hs

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
