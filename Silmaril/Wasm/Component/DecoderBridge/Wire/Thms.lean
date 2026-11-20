module

public import Silmaril.Wasm.Component.DecoderBridge.Wire.Defs
public import Silmaril.Wasm.Component.InstTestsRef.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Wire

/-!
# The two readings of a component binary agree on wiring, imports and exports (fragment)

All proved; proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Wire`.

* `relW_of_decode`: **for every binary `b`** whose IR reading `Binary.parseComponent b = .ok c`
  and REF reading `Conformance.decodeRef b = .ok r` both succeed, with `r` in the fragment
  (`InFrag r`, decidable), `RelW c r`: the IR component's imports and exports are those the
  reference component's definitions name (`refRead`), and node `k` of the IR is the core
  instance of a module whose bytes decode to the module of the reference's `k`-th core
  instantiation, with that module's interface, wired to what the instantiation's arguments name
  (by name, the first match, as the reference machine resolves them). Together with
  `DecoderBridge.rel_of_decode` (which holds without the fragment).
* `starts_inFrag`, `trap_inFrag` (kernel, `decide +kernel`) and `starts_relW`, `trap_relW`: the
  two test binaries are in the fragment.

**Scope.** This is a statement about syntax: the wiring both readings name. That the reference
machine's instantiation follows the symbolic reading `refRead` (the index spaces it builds at
run time), and anything about behaviour, is not proved: the behavioural statements are the open
goals of `DecoderBridge.Sem`. The fragment excludes instance exports, among other forms (see
`Wire.Defs`); on them the two readings name different exports (`DecoderBridge.InstExport`).
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef

/-- **Whenever both readings of a binary succeed and the REF reading is in the fragment, they
agree on wiring, imports and exports.** -/
theorem relW_of_decode {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hf : InFrag r) :
    RelW c r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.relW_of_decode hc hr hf

/-- `starts.wasm` is in the fragment. -/
theorem starts_inFrag : InFrag startsRef := by decide +kernel

/-- `trap.wasm` is in the fragment. -/
theorem trap_inFrag : InFrag trapRef := by decide +kernel

/-- `starts.wasm`: an instance of `relW_of_decode`. -/
theorem starts_relW : RelW startsComp startsRef :=
  relW_of_decode parse_starts decodeRef_starts starts_inFrag

/-- `trap.wasm`: an instance of `relW_of_decode`. -/
theorem trap_relW : RelW trapComp trapRef :=
  relW_of_decode parse_trap decodeRef_trap trap_inFrag

end Silmaril.Wasm.Component.DecoderBridge
