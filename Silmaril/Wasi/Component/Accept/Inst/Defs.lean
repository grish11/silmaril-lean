module

public import Silmaril.Wasi.Component.Accept.Consequence.Defs
public import Silmaril.Wasm.Component.InstExport.Defs
public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs

/-! # Component acceptors with an instantiation phase

The acceptors of `Silmaril.Wasi.Component.Accept` read an IR component through its start-free
denotation `Comp.denU C c` (`Layout.compModel`). Under the execution-based core semantics
`Binary.coreModSem P` a lowered core module **with a start function** has no instance there and
traps on every question, so a component whose core modules have start functions is not read
faithfully.

This module gives the instantiation-aware counterparts. They read a component through the
**export phase** of its instantiating denotation, `Comp.denX C c = exportPhase (c.denI C)`
(`Silmaril.Wasm.Component.InstExport`): the plays after a successful instantiation
`[inst] ++ cs ++ [ready]` (start functions run in program order, their import calls answered
by the environment in any way), as plays of the start-free interface.

* `Layout.compModelI C L c = L.view (c.denX C)`: the WASI model of the export phase;
* `ComponentAcceptor.ofIRI C L c …`: the acceptor of that model. Its language
  (`ComponentAcceptor.langI`) is **ready-then-export acceptance**: the bytes accepted
  (through the imported `accept` called with them, or the exported `accept` returning `true`
  on them) in some play after a successful instantiation. A component whose instantiation
  never succeeds (a trapping start function, a module without an instance) accepts nothing.
  Import calls made *during* instantiation are not plays of the export phase: a start function
  calling `accept` is not counted.
* `ComponentAcceptor.ofCompI C c mode`: through the component's own names (`Layout.ofComp`);
* `componentBytesSystemI C mode`: component binaries (`ComponentAcceptor.decodeBinary`) read by
  `ofCompI C`;
* `componentBytesSystemCore3I P mode = componentBytesSystemI (Binary.coreModSemI P) mode`:
  **the binary path with faithful start functions**: bytes, parsed and lowered
  (`parseComponent`), core modules run on Core 3.0 at profile `P` with their start functions at
  instantiation (`Binary.coreModSemI`), components instantiated in program order
  (`Comp.denI`), accepted after a successful instantiation.

The existing names keep their meaning: `ComponentAcceptor.ofIR`, `lang`, `componentBytesSystem`
and `componentBytesSystemCore3` still read `Comp.denU` over a start-free `CoreSem`. For a
start-free core semantics the two readings coincide (`ofIRI_toI`); for the Core 3.0 pipeline
on lowered components whose core modules all have an instance and no start function, the
instantiation-aware language is included in the start-free one (`Accept.Inst.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasi

open Silmaril.Wasm.Component

/-- **A component with an instantiation phase as a WASI model**: the view of its export
phase. -/
def Layout.compModelI {M : Type} [CoreModule M] (C : CoreSemI M) (L : Layout) (c : Comp M) :
    L.world.Model :=
  L.view (c.denX C)

namespace Accept

open Silmaril.Consequence (System)

namespace ComponentAcceptor

/-- **The acceptor of an IR component with an instantiation phase** under a layout: the
acceptor of its export phase. -/
def ofIRI {M : Type} [CoreModule M] (C : CoreSemI M) (L : Layout) (c : Comp M)
    (accept : FnName := acceptFn) (reject : Option FnName := none) (mode : Mode := .imp) :
    ComponentAcceptor :=
  ⟨_, _, L.compModelI C c, accept, reject, mode⟩

/-- **Ready-then-export acceptance**: the bytes accepted after a successful instantiation. -/
def langI {M : Type} [CoreModule M] (C : CoreSemI M) (L : Layout) (c : Comp M)
    (accept : FnName := acceptFn) (reject : Option FnName := none) (mode : Mode := .imp) :
    Silmaril.Formats.Accept.ByteLang :=
  (ofIRI C L c accept reject mode).lang

/-- The component `c` with an instantiation phase, read through its own names, with the
world-level `accept` function. -/
def ofCompI {M : Type} [CoreModule M] (C : CoreSemI M) (c : Comp M) (mode : Mode := .imp) :
    ComponentAcceptor :=
  ofIRI C (Layout.ofComp c) c acceptFn none mode

end ComponentAcceptor

/-- **Component binaries with an instantiation phase as a consequence system**: `b ⊢ w` iff `b`
parses and lowers to a component `c` that, under the core semantics `C`, accepts `w` after a
successful instantiation (`ComponentAcceptor.ofCompI`). The decoding restrictions of
`componentBytesSystem` apply (fixed-arity `accept`). -/
def componentBytesSystemI (C : CoreSemI Silmaril.Wasm.Component.Binary.CoreMod)
    (mode : Mode := .imp) : System ByteArray (List UInt8) :=
  System.ofDecoder ComponentAcceptor.decodeBinary fun c => ComponentAcceptor.ofCompI C c mode

/-- **Component binaries, executing their core modules with their start functions**:
`componentBytesSystemI` at `Binary.coreModSemI P` (Core 3.0 at profile `P`). -/
noncomputable def componentBytesSystemCore3I
    (P : Silmaril.Wasm.Numerics.Profile := Silmaril.Wasm.Numerics.Profile.spec)
    (mode : Mode := .imp) : System ByteArray (List UInt8) :=
  componentBytesSystemI (Silmaril.Wasm.Component.Binary.coreModSemI P) mode

end Accept

end Silmaril.Wasi
