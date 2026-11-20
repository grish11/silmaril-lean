module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Lower
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.ToRef

/-!
# The two readings of a component binary agree on core instantiations

* `decoders_factor`: both readings go through one AST: if `Binary.parseComponent b = .ok c` and
  `Conformance.decodeRef b = .ok r`, then `Binary.parse b = .ok a` with `Binary.lower a = .ok c`
  and `Conformance.toRef a = .ok r`;
* `rel_of_decode`: then `DecoderBridge.Rel c r` (`lower_ok`, `toRef_ok`, `coreMod_ok`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge

theorem decoders_factor {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) :
    ∃ a, Binary.parse b = .ok a ∧ Binary.lower a = .ok c ∧ toRef a = .ok r := by
  unfold Binary.parseComponent at hc
  unfold decodeRef at hr
  cases hp : Binary.parse b with
  | error e => simp [hp] at hr
  | ok a =>
    simp only [hp] at hc hr
    exact ⟨a, rfl, hc, hr⟩

theorem rel_of_decode {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) : Rel c r := by
  obtain ⟨a, -, hl, ht⟩ := decoders_factor hc hr
  obtain ⟨hn, hs⟩ := lower_ok hl
  obtain ⟨hsp, hri⟩ := toRef_ok ht hs
  unfold Rel
  rw [hri, hsp]
  refine hn.imp ?_
  rintro n e ⟨bs, m, w, hb, hm, rfl⟩
  obtain ⟨hmb, d, hd⟩ := coreMod_ok hm
  exact ⟨m, w, d, rfl, by simp [hb, hd], by rw [hmb]; exact hd⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge
