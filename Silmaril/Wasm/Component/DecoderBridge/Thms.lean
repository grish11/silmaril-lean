module

public import Silmaril.Wasm.Component.DecoderBridge.Defs
public import Silmaril.Wasm.Component.InstTestsRef.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Bridge

/-!
# The two readings of a component binary agree on core instantiations

All proved, for **every** byte string; proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge`.

* `decoders_factor`: the IR reading `Binary.parseComponent` and the REF reading
  `Conformance.decodeRef` go through one AST: when both succeed on `b`, `Binary.parse b = .ok a`,
  `Binary.lower a` is the IR component and `Conformance.toRef a` the reference component.
* `lower_nodes` (IR side): the nodes `Binary.lower a` produces are, in order, one core node per
  top-level core `instantiate` of `a`, over the module `Binary.Lower.coreMod` reads from the
  core module section at the instantiation's index; and `a` has no top-level import, alias or
  export of the core module sort. `coreMod_bytes`: such a module keeps its bytes, which the core
  decoder accepts.
* `toRef_insts` (REF side): if `a` has no top-level import, alias or export of the core module
  sort, the core module index space of `Conformance.toRef a` is the core decoder's reading of
  `a`'s core module sections, and its core instantiations are those of `a`.
* `rel_of_decode`: **if both readings of `b` succeed, they are related by `Rel`**: the IR nodes
  and the reference's core instantiations correspond one to one, in order, and each IR node is
  a core node over a module whose bytes the core decoder reads as the reference module the
  corresponding instantiation names.
* `starts_rel`, `trap_rel`: the two test binaries, as instances of `rel_of_decode` (from
  `InstTests.parse_starts`/`parse_trap` and `InstTestsRef.decodeRef_starts`/`decodeRef_trap`).

**Scope.** `Rel` relates the structure that instantiation runs: which core modules are
instantiated, in which order, from which bytes. It does not relate the IR's wiring programs to
the reference's instantiation arguments (the reference keeps the arguments, the IR resolves them
by name), canonical definitions, types, imports or exports, and it says nothing about behaviour.
Neither reading's success implies the other's: `lower` rejects most of the component model
(see `Binary.Lower.Defs`), and `toRef` rejects some forms `lower` ignores (for instance type
definitions `lower` records as unsupported but never uses). For a decidable fragment of the
reference syntax, `DecoderBridge.Wire` relates the wiring, imports and exports too
(`relW_of_decode`). The behavioural statements are `DecoderBridge.Sem`.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef

/-- **Both readings share the parser.** -/
theorem decoders_factor {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) :
    ∃ a, Binary.parse b = .ok a ∧ Binary.lower a = .ok c ∧ toRef a = .ok r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.decoders_factor hc hr

/-- **The IR nodes are the core instantiations, over the decoded core module sections.** -/
theorem lower_nodes {a : Binary.Ast} {c : Comp Binary.CoreMod} (h : Binary.lower a = .ok c) :
    List.Forall₂ (fun n e => ∃ bs m w, (modBytes a.sections)[e.1]? = some bs ∧
        Binary.Lower.coreMod bs = .ok m ∧ n = .core m w) c.nodes (instExprs a.sections) ∧
      noModuleSort a.sections = true :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.lower_ok h

/-- An embedded core module of the IR keeps its bytes, which the core decoder accepts. -/
theorem coreMod_bytes {bs : ByteArray} {m : Binary.CoreMod} (h : Binary.Lower.coreMod bs = .ok m) :
    m.bytes = bs ∧ ∃ d, Silmaril.Wasm.Binary.Core.decode? bs = some d :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.coreMod_ok h

/-- **The reference's core modules and core instantiations are those of the AST.** -/
theorem toRef_insts {a : Binary.Ast} {r : RefComponent} (h : toRef a = .ok r)
    (hn : noModuleSort a.sections = true) :
    coreModSpace r = (modBytes a.sections).map Silmaril.Wasm.Binary.Core.decode? ∧
      refInsts r = instExprs a.sections :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.toRef_ok h hn

/-- **Whenever both readings of a binary succeed, they agree on core instantiations.** -/
theorem rel_of_decode {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) : Rel c r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.rel_of_decode hc hr

/-- `starts.wasm`: an instance of `rel_of_decode`. -/
theorem starts_rel : Rel startsComp startsRef := rel_of_decode parse_starts decodeRef_starts

/-- `trap.wasm`: an instance of `rel_of_decode`. -/
theorem trap_rel : Rel trapComp trapRef := rel_of_decode parse_trap decodeRef_trap

end Silmaril.Wasm.Component.DecoderBridge
