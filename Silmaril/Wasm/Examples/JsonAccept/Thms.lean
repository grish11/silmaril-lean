module

public import Silmaril.Wasm.Examples.JsonAccept.Defs
public import Silmaril.Wasm.Abstract.AcceptWasm.Thms
public import Silmaril.Formats.JsonBytes.Thms
public import Silmaril.Formats.Accept.Format.Thms
import Silmaril.Proofs.Wasm.Examples.JsonAccept.Basic

/-! # A concrete Wasm acceptor for a JSON subset: theorems

`prog`'s `accept(ptr, len)` is verified against Core 3.0 small-step execution
(`Execution.Core.Steps`), at every numerics profile and every host relation, for every input:

* `accept_verified`: function `0` meets `spec` (the `wpc` verification condition, `spec_vc`).
* `accept_returns`: every run of `$invoke` on in-bounds `(ptr, len)` that returns gives `1` iff
  the segment is an integer text, else `0`, and leaves the store unchanged.
* **Soundness against JSON**: a run returning `1` read a JSON text (`accept_sound_json`; through
  Core `behaviours`, `accept_sound_json_behaviours`).
* **Exactness for the subset**: on in-bounds arguments, a returning run gives `1` iff the
  segment lies in `intText` (`accept_returns_one_iff`). So the function never rejects an integer
  text, and accepts nothing else.
* **The abstract acceptor is sound too**: through the commuting diagram of
  `Silmaril.Wasm.Abstract.AcceptWasm` (`retAcceptsSome_wasmFun`), the export acceptor of the
  abstract function `wasmFun` only accepts arguments whose segment is JSON
  (`abstract_accept_sound_json`).

**Scope.** This decides `intText`, the JSON texts that are one integer with surrounding
whitespace. It is **a subset of JSON**, not a JSON validator: it rejects every other JSON
text (fractions, exponents, strings, literals, arrays, objects), so it is incomplete for JSON.
The proofs are **partial correctness**: a run that returns returns the right answer, and no run
traps or gets stuck. Termination is not proved, so "accepts every integer text" means "never
answers `0` on one".
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Proofs.Wasm.Examples.JsonAccept
open Silmaril.Wasm.Numerics (Profile)

/-- **`accept` meets its specification.** -/
theorem accept_verified : Verified prog 0 spec := ⟨_, rfl, spec_vc⟩

/-- The automaton accepts exactly the integer texts. -/
theorem acc_iff (w : List UInt8) :
    (2 ≤ runN 0 (w.map UInt8.toNat) ∧ runN 0 (w.map UInt8.toNat) ≤ 4) ↔ w ∈ intText :=
  ⟨fun h => rest_of_acc 0 w h, acc_of_intText⟩

/-- The integer texts are JSON texts. -/
theorem intText_le_json (p : Silmaril.Formats.JsonBytes.Profile) :
    intText ≤ Silmaril.Formats.JsonBytes.language p :=
  intText_le_language p

/-- The segment's byte values are the memory's. -/
theorem bytesN_eq_segment (B : ByteArray) (a k : Nat) :
    bytesN B a k = (segment B a k).map UInt8.toNat := by
  simp only [segment, bytesN, List.map_map]
  congr 1; funext j
  simp [Function.comp_def]

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
  {ps rs : Validation.Ty (.list .val)} {ma : Nat} {mt : MemoryType} {B : ByteArray}
  {p n : BitVec 32}

/-- **Every returning run of `accept`** answers by the automaton and leaves the store unchanged. -/
theorem accept_returns (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals res⟩) :
    s' = s ∧ res = [.i32 (if 2 ≤ runN 0 (bytesN B p.toNat n.toNat) ∧
      runN 0 (bytesN B p.toNat n.toNat) ≤ 4 then 1 else 0)] := by
  have hv := FnSpec.sound (P := P) (host := host) (a := a) spec_vc hc he (fun _ => by simp [spec, Silmaril.Wasm.Verify.FnSpec.mem, hps])
    (by simpa [spec, Silmaril.Wasm.Verify.FnSpec.mem] using hrs) (p, n)
  obtain ⟨res', hres, hpost⟩ := Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals hv
    ⟨hfi, rfl, ma, mt, B, hmem, hb, hov⟩ hs
  cases hres
  obtain ⟨hs', hr⟩ := hpost ma mt B hmem
  exact ⟨hs'.trans (setMem_eq_self hmem.2), hr⟩

/-- **A returning run answers `1` iff the segment is an integer text.** -/
theorem accept_returns_one_iff (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm prog.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hmem : MemAt s fi.module ma mt B) (hb : p.toNat + n.toNat ≤ B.size)
    (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals res⟩) :
    res = [.i32 1] ↔ segment B p.toNat n.toNat ∈ intText := by
  obtain ⟨-, hr⟩ := accept_returns hfi hc he hps hrs hmem hb hov hs
  rw [hr, ← acc_iff, ← bytesN_eq_segment]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

/-- **Soundness against JSON**: a run of `accept` returning `1` read a JSON text. -/
theorem accept_sound_json (q : Silmaril.Formats.JsonBytes.Profile) (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hb : p.toNat + n.toNat ≤ B.size) (hov : p.toNat + n.toNat < 2 ^ 32) {s' : Store Nat}
    {f' : Frame} (hs : Steps P host (invoke s a [.i32 p, .i32 n]) ⟨s', f', vals [.i32 1]⟩) :
    segment B p.toNat n.toNat ∈ Silmaril.Formats.JsonBytes.language q :=
  intText_le_json q ((accept_returns_one_iff hfi hc he hps hrs hmem hb hov hs).1 rfl)

/-- The same, through Core `behaviours`. -/
theorem accept_sound_json_behaviours (q : Silmaril.Formats.JsonBytes.Profile) (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hb : p.toNat + n.toNat ≤ B.size) (hov : p.toNat + n.toNat < 2 ^ 32)
    (hbeh : Behaviour.returns [.i32 1] ∈ behaviours P host s a [.i32 p, .i32 n]) :
    segment B p.toNat n.toNat ∈ Silmaril.Formats.JsonBytes.language q := by
  rcases hbeh with ⟨⟨s', f', code⟩, r, hs, hcode, hr⟩ | ⟨h, -⟩
  · cases r with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hr
      subst hr
      simp only [Result.toAdmin] at hcode
      subst hcode
      exact accept_sound_json q hfi hc he hps hrs hmem hb hov hs
    | trap => cases hr
    | throw _ => cases hr
  · cases h

/-- **The abstract export acceptor of `accept` is sound for JSON**: an argument list the
abstract function `wasmFun` may answer with `1` from the store `s` has a JSON segment. -/
theorem abstract_accept_sound_json (q : Silmaril.Formats.JsonBytes.Profile) (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hb : p.toNat + n.toNat ≤ B.size) (hov : p.toNat + n.toNat < 2 ^ 32)
    (h : [.i32 p, .i32 n] ∈ Silmaril.Wasm.Abstract.Accept.retAcceptsSome
      (Silmaril.Wasm.Abstract.wasmFun P host a) {s}
      (Silmaril.Wasm.Abstract.endToBehaviour ⁻¹' {Behaviour.returns [.i32 1]})) :
    segment B p.toNat n.toNat ∈ Silmaril.Formats.JsonBytes.language q := by
  rw [Silmaril.Wasm.Abstract.Accept.retAcceptsSome_wasmFun] at h
  obtain ⟨b, ⟨s₀, hs₀, hb'⟩, hacc⟩ := h
  rw [Set.mem_singleton_iff.1 hs₀] at hb'
  rw [Set.mem_singleton_iff.1 hacc] at hb'
  exact accept_sound_json_behaviours q hfi hc he hps hrs hmem hb hov hb'

/-- **The acceptor is sound for the JSON format** (`Silmaril.Formats.Format.ofLanguage`): what it
accepts is a valid input of the format. -/
theorem accept_sound_jsonFormat (q : Silmaril.Formats.JsonBytes.Profile)
    (hfi : s.funcs[a]? = some fi)
    (hc : fi.code = .wasm prog.funcs[0]) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) (hmem : MemAt s fi.module ma mt B)
    (hb : p.toNat + n.toNat ≤ B.size) (hov : p.toNat + n.toNat < 2 ^ 32)
    (hbeh : Behaviour.returns [.i32 1] ∈ behaviours P host s a [.i32 p, .i32 n]) :
    segment B p.toNat n.toNat ∈
      (Silmaril.Formats.Format.ofLanguage (Silmaril.Formats.JsonBytes.language q)).lang := by
  rw [Silmaril.Formats.Format.lang_ofLanguage]
  exact accept_sound_json_behaviours q hfi hc he hps hrs hmem hb hov hbeh

/-! ## The subset on examples (the specification, by evaluation) -/

example : "-42".toUTF8.data.toList ∈ intText :=
  (acc_iff _).1 (by decide)

example : " 0 ".toUTF8.data.toList ∈ intText := (acc_iff _).1 (by decide)

example : "007".toUTF8.data.toList ∉ intText := fun h => by
  have := (acc_iff _).2 h
  revert this; decide

example : "4 2".toUTF8.data.toList ∉ intText := fun h => by
  have := (acc_iff _).2 h
  revert this; decide

/-- `[1]` is JSON but not an integer text: the acceptor is incomplete for JSON. -/
example : "[1]".toUTF8.data.toList ∉ intText := fun h => by
  have := (acc_iff _).2 h
  revert this; decide

end Silmaril.Wasm.Examples.JsonAccept
