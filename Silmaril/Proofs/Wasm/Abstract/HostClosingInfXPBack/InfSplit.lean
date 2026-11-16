module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.DivWhole

/-!
# Productive runs: splitting at a handler, and finished runs (proofs)

* `coreInf_handler_seq_split`: a productive run of a `try_table` handler in place runs
  productively in its body, or the body runs to a stuck end that is not at a host call with a
  prefix of the stream, and the handler around that end runs productively (the handler analogue
  of `coreInf_label_seq_split`, by `coreInf_wrap_split`);
* `noInf_of_evRun` (deterministic profile): a labelled run to a configuration with no step rules
  out a productive run whose stream starts with that run's log;
* `coreInf_drop`: the stream of a productive run after an answered host call event.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded
open Shape (streamAppend)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **Splitting a productive run of a handler in place.** -/
theorem coreInf_handler_seq_split {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host ⟨s, f, vals ws ++ [.handler n cs₀ b] ++ rest⟩ ω) :
    CoreInf P host ⟨s, f, b⟩ ω ∨
      ∃ (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)) (cb : Config H)
        (N₁ : Nat), ω = cs₁ ++ω ω₂ ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        CoreInf P host ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩ ω₂ := by
  have hW : ∀ y y' : Config H,
      (⟨y.store, y.frame, vals ws ++ [.handler n cs₀ y.code] ++ rest⟩ : Config H) =
        ⟨y'.store, y'.frame, vals ws ++ [.handler n cs₀ y'.code] ++ rest⟩ → y = y' := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
    simp only [Config.mk.injEq, List.append_cancel_right_eq, List.append_cancel_left_eq,
      List.cons.injEq, Admin.handler.injEq, and_true, true_and] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  refine (coreInf_split_wrap (P := P) (host := host)
      (fun y => ⟨y.store, y.frame, vals ws ++ [.handler n cs₀ y.code] ++ rest⟩) hW
      (fun cs₁ d => ∃ (cb : Config H) (N₁ : Nat), EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        d = ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ cb.code] ++ rest⟩)
      (y₀ := ⟨s, f, b⟩) ?_ h).imp id ?_
  swap
  · rintro ⟨cs₁, ω₂, d, hω, ⟨cb, N₁, h₁, hs, hdc, rfl⟩, hd⟩
    exact ⟨cs₁, ω₂, cb, N₁, hω, h₁, hs, hdc, hd⟩
  intro y cs₀' k c z e hr hk he
  obtain ⟨cb, N₁, cs₁, cs₂, hcs, -, hb, hsb, hk', hx⟩ :=
    evRunN_handler_seq_split hk (noFree_of_event he)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hcs.symm
  cases hdc : decompose? cb.store cb.code with
  | none =>
    obtain ⟨N₂, hN₂⟩ := evRunN_of_evRun (by simpa using evRun_trans hr (evRunN_evRun hb))
    exact .inr ⟨_, ⟨cb, N₂, hN₂, hsb, hdc, rfl⟩,
      by simpa using evRun_trans (evRunN_evRun hk') (.event he (.refl _))⟩
  | some yy =>
    have hsome : (decompose? cb.store cb.code).isSome := by rw [hdc]; rfl
    obtain ⟨-, rfl⟩ := hx hsome
    obtain ⟨s', f', b', rfl, he'⟩ := hEvStep_handler_inv hsome he
    exact .inl ⟨cb, ⟨s', f', b'⟩, evRunN_evRun hb, he', rfl⟩

theorem silent_evRunN' {x y : Config H}
    (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) x y) :
    ∃ k, EvRunN P host k x [] y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .silent hs hk⟩

/-- **Through an answered host call**, the rest of the stream runs productively after it. -/
theorem coreInf_event {K K₁ : Config H} {e : Call (wasmHostSig H)}
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host K ([e] ++ω ω))
    (he : HEvStep P host K (some e) K₁) : CoreInf P host K₁ ω := by
  obtain ⟨g, hg0, hg⟩ := h
  obtain ⟨c₁, hs, he₁⟩ := hg 0
  rw [hg0] at hs
  obtain ⟨E, a, hdK, -⟩ := id he
  have hc₁ : c₁ = K := by
    obtain ⟨k, hk⟩ := silent_evRunN' hs
    exact evRunN_nil_at_host hdK hk
  subst hc₁
  have h0 : ([e] ++ω ω) 0 = e := by rw [Shape.streamAppend_lt (by simp)]; rfl
  rw [h0] at he₁
  obtain rfl := hEvStep_some_det he₁ he
  refine ⟨fun n => g (n + 1), rfl, fun n => ?_⟩
  have := hg (n + 1)
  rwa [Shape.streamAppend_ge (by simp), List.length_singleton,
    show n + 1 - 1 = n by omega] at this

section Det

variable {o : GrowOracle}

/-- **A labelled run to a configuration with no step rules out a productive run** whose stream
starts with the run's log (deterministic profile). -/
theorem noInf_of_evRun {K X : Config H} {q : List (Call (wasmHostSig H))}
    (hf : EvRun (profile o) host K q X) (hX : ∀ c', ¬ Step (profile o) host X c')
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf (profile o) host K (q ++ω ω)) : False := by
  induction hf with
  | refl => exact coreInf_no_step hX (by simpa [Shape.streamAppend_nil] using h)
  | @silent K K₁ X q hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact ih hX (coreInf_through_dsteps (.single hs) h)
    · exact ih hX h
  | @event K K₁ X e q hs _ ih =>
    refine ih hX (coreInf_event (e := e) ?_ hs)
    rw [← Shape.streamAppend_append]
    exact h

end Det

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
