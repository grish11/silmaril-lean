module

public import Silmaril.Wasm.Interp.CtxInv.Defs
public import Silmaril.Wasm.Abstract.BackInv.Defs
public import Silmaril.Wasm.Interp.PProgress.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms

/-!
# The invariant of the backward simulations: divergence facts (proofs)

For every `BackInv`: host-free divergence passes through host-free runs
(`BackInv.diverges_through_steps`), labelled divergence too (`BackInv.evDiv_through_steps`), and a
productive run is not host-free divergence (`BackInv.coreInf_not_diverges`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.BackInv

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} (K : BackInv H) {o : GrowOracle} {host : HostSemantics H}

/-- **A divergent run passes through every host-free run** of a configuration in the
invariant. -/
theorem diverges_through_steps {K₀ T : Config H}
    (hpred : Relation.ReflTransGen (SingleThreaded.Det.DStep o) K₀ T) (ht : K.CT K₀)
    (hK : Diverges (profile o) host K₀) : Diverges (profile o) host T := by
  induction hpred with
  | refl => exact hK
  | tail hst h ih => exact K.through (K.steps ht hst) ih h

/-- **Labelled divergence passes through host-free runs**, with the same log. -/
theorem evDiv_through_steps {n : Nat} {K₀ T : Config H} {cs : List (Call (wasmHostSig H))}
    (hpred : Relation.ReflTransGen (SingleThreaded.Det.DStep o) K₀ T) (ht : K.CT K₀)
    (h : EvDiv (profile o) host n K₀ cs) : EvDiv (profile o) host n T cs := by
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · exact .inl ⟨rfl, K.diverges_through_steps hpred ht hd⟩
  · have hfree : ∀ c'', ¬ Step (profile o) SingleThreaded.Det.noHost c₀ c'' := by
      obtain ⟨E, a, hdec, -⟩ := he
      exact fun c'' => noFree_of_decompose hdec
    obtain ⟨m, hm, h⟩ := evRunN_through_steps hpred hr hfree
    exact .inr ⟨m, cs₀, e, c₀, c₁, hm.trans hk, rfl, h, he, hd⟩

/-- **A productive run is not host-free divergence**, from a configuration in the invariant. -/
theorem coreInf_not_diverges {c : Config H} {ω : Nat → Call (wasmHostSig H)} (ht : K.CT c)
    (hd : Diverges (profile o) SingleThreaded.Det.noHost c)
    (h : CoreInf (profile o) host c ω) : False := by
  obtain ⟨g, hg0, hg⟩ := h
  obtain ⟨c₁, hs, he⟩ := hg 0
  rw [hg0] at hs
  obtain ⟨b, hb, -⟩ := (K.diverges_through_steps (silentRun_dsteps hs) ht hd).unfold
  obtain ⟨E, a, hdec, -⟩ := he
  exact noFree_of_decompose hdec hb

end Silmaril.Wasm.Interp.BackInv
