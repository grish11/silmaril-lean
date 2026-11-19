module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Init
public import Silmaril.Wasm.Interp.CtxInv.Defs
public import Silmaril.Wasm.Abstract.BackInv.Thms

/-!
# The relaxed invariant is an invariant of the backward simulations (proofs)

`ConfigOkD` against `HostTypedD` hosts has every operation of `Interp.BackInv`:

* the context decompositions (`ConfigOkD.suffix`, `.label`, `.handler`, `.frame`): the hole of a
  context in the supported profile is supported, and the witness types it in context;
* host-free steps (`ConfigOkD.step`) and runs against a `HostTypedD` host
  (`ConfigOkD.steps_host`, through `ConfigOkD.evRun`); a host also answering one call by a trap
  in its store is still `HostTypedD` (`hostTypedD_trapAt`);
* the witness (`ConfigOkD.wit`): `gst s T X` with tags extending the store's, on which every
  defined-type cast decides as on the actual store (`refOk_gst_iff`: the cast is supported);
* divergence through host-free steps (`ConfigOkD.through`), by `diverges_through_of`: the actual
  store has closed-valid principal types (`storeTy_of_ghost`: the principal type of an existing
  exception is `exnref`, every other reference has its witness type), and the code meets the
  cast side conditions (read off the witness's typing; they are about frame and code only).
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Cfg.DanglingTyped
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type}

/-! ## Context decompositions -/

theorem ConfigOkD.suffix {s : Store H} {f : Frame} {body rest : List Admin}
    (h : ConfigOkD ⟨s, f, body ++ rest⟩) : ConfigOkD ⟨s, f, body⟩ := by
  obtain ⟨hF, hfr, hc, hh, T, X, hg, ht⟩ := h
  exact ⟨hF, hfr, fun a ha => hc a (List.mem_append_left _ ha), hh, T, X, hg,
    Sim.ContextTyped.suffix ht⟩

theorem ConfigOkD.label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
    {body rest : List Admin} (h : ConfigOkD ⟨s, f, vals vs ++ [.label n cont body] ++ rest⟩) :
    ConfigOkD ⟨s, f, body⟩ := by
  obtain ⟨hF, hfr, hc, hh, T, X, hg, ht⟩ := h
  have hl := hc (.label n cont body) (by simp)
  refine ⟨hF, hfr, ?_, hh, T, X, hg, Sim.ContextTyped.label ht⟩
  cases hl with
  | label _ _ hb => exact hb

theorem ConfigOkD.handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
    {body rest : List Admin} (h : ConfigOkD ⟨s, f, vals vs ++ [.handler n cs body] ++ rest⟩) :
    ConfigOkD ⟨s, f, body⟩ := by
  obtain ⟨hF, hfr, hc, hh, T, X, hg, ht⟩ := h
  have hl := hc (.handler n cs body) (by simp)
  refine ⟨hF, hfr, ?_, hh, T, X, hg, Sim.ContextTyped.handler ht⟩
  cases hl with
  | handler _ _ hb => exact hb

theorem ConfigOkD.frameHole {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val}
    {body rest : List Admin} (h : ConfigOkD ⟨s, f, vals vs ++ [.frame n fi body] ++ rest⟩) :
    ConfigOkD ⟨s, fi, body⟩ := by
  obtain ⟨hF, hfr, hc, hh, T, X, hg, ht⟩ := h
  have hl := hc (.frame n fi body) (by simp)
  cases hl with
  | frame _ hf hb => exact ⟨hF, hf, hb, hh, T, X, hg, Sim.ContextTyped.frame ht⟩

/-! ## The witness -/

theorem ConfigOkD.wit {c : Config H} (h : ConfigOkD c) :
    ∃ (T : List TagInst) (X : List ExnInst), c.store.tags <+: T ∧
      (∀ (m : ModuleInst) (r : Ref) (b : Bool) (y : TypeIdx),
        RefOk { c.store with tags := T, exns := X } r (m.instRef ⟨b, .typeIdx y⟩) ↔
          RefOk c.store r (m.instRef ⟨b, .typeIdx y⟩)) ∧
      Sim.ContextTyped ⟨{ c.store with tags := T, exns := X }, c.frame, c.code⟩ := by
  obtain ⟨T, X, hg, ht⟩ := h.ghost
  exact ⟨T, X, hg.tags, fun _ _ _ _ => refOk_gst_iff hg (fun h => h), ht⟩

/-! ## Runs against store-keeping hosts with typed values -/

theorem ConfigOkD.steps_host {P : Profile} {host : HostSemantics H} (hT : HostTypedD host)
    {c c' : Config H} (hc : ConfigOkD c) (h : Steps P host c c') : ConfigOkD c' := by
  induction h with
  | refl => exact hc
  | tail _ hst ih =>
    obtain ⟨e, he⟩ := Abstract.step_hEvStep hst
    cases e with
    | none => exact ConfigOkD.evRun hT ih (.silent he (.refl _))
    | some e => exact ConfigOkD.evRun hT ih (.event he (.refl _))

theorem hostTypedD_trapAt {host : HostSemantics H} (m : H × Store H × List Val)
    (hT : HostTypedD host) : HostTypedD (Interp.trapAt host m) := by
  intro hh s us s' r h
  rcases h with h | ⟨-, rfl, -, he⟩
  · exact hT _ _ _ _ _ h
  · cases he
    exact ⟨rfl, fun _ _ _ _ _ _ => trivial⟩

/-! ## Divergence through host-free steps -/

/-- **The actual store of a witness has closed-valid principal types.** -/
theorem storeTy_of_ghost {s : Store H} {T : List TagInst} {X : List ExnInst} (hg : GhostOk s T X)
    (hW : Abstract.StoreTy (gst s T X)) : Abstract.StoreTy s := by
  intro r rt₀ e
  by_cases hr : ∃ a, r = .exn a
  · obtain ⟨a, rfl⟩ := hr
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ex, hex, rfl⟩ := e
    obtain ⟨e', he', -⟩ := hg.real a ex hex
    exact hW (.exn a) _ (by simp [Ref.type?, he'])
  · apply hW r rt₀
    cases r <;> first | exact e | exact absurd ⟨_, rfl⟩ hr

theorem ConfigOkD.storeTy_deepAll {c : Config H} (h : ConfigOkD c) :
    Abstract.StoreTy c.store ∧
      SingleThreaded.Exec.DeepAll SingleThreaded.Exec.IHeadInv c.frame c.code := by
  obtain ⟨T, X, hg, ht⟩ := h.ghost
  obtain ⟨hW, hi⟩ := Interp.BackInv.storeTy_deepAll_of_ctx ht
  exact ⟨storeTy_of_ghost hg hW, hi⟩

/-- **Divergence passes through every host-free step** of a configuration in the relaxed
invariant (deterministic profile). -/
theorem ConfigOkD.through {o : GrowOracle} {host : HostSemantics H} {K d : Config H}
    (ht : ConfigOkD K) (hK : Diverges (profile o) host K) (hd : SingleThreaded.Det.DStep o K d) :
    Diverges (profile o) host d :=
  Interp.BackInv.diverges_through_of (fun _ h => ConfigOkD.storeTy_deepAll h)
    (fun _ _ h hs => ConfigOkD.step h hs) ht hK hd

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
