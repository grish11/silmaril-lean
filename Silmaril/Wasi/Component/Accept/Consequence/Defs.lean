module

public import Silmaril.Wasi.Component.Accept.Acceptor.Defs
public import Silmaril.Wasm.Game.Accept.Consequence.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs

/-! # Component acceptors, and acceptors of either shape, as consequence systems

The three views of `Silmaril.Logic.Consequence.Acceptor` for components, and for Wasm
programs of either shape (`Silmaril.Wasm.Game.Accept.ModuleAcceptor` gives them for modules):

| view | definition | contexts |
|---|---|---|
| acceptor | `System.ofAcceptor ComponentAcceptor`, `System.ofAcceptor ByteAcceptor` | acceptors |
| program | `ComponentAcceptor.compSystem C L`, `ByteAcceptor.programSystem A I` | `Comp M`; `Module ⊕ W` |
| bytes | `ComponentAcceptor.bytesSystem decode C L`, `ComponentAcceptor.binarySystem C L`, `ByteAcceptor.bytesSystem A C L` | bytes |

**The component interpreter** `ComponentAcceptor.interp C L acc rej mode` reads an IR component
`c : Comp M` as `ComponentAcceptor.ofIR C L c acc rej mode`: the core semantics `C`, the layout
`L` naming its import and export positions, the `accept`/`reject` functions and their mode are
the interpretation.

**Component bytes.** `binarySystem` decodes with the driver
`Silmaril.Wasm.Component.Binary.parseComponent` into `Comp CoreMod`. Its parsing is verified,
its lowering is partial (no list, string or resource types) and unverified. The only core
semantics of the lowered modules in the library is the loosest
(`Silmaril.Project.WasmComponents.topSem`), so `C` is a parameter. `bytesSystem` takes any decoder.

**Simple entry points.** `componentBytesSystem C` reads component binaries only, through their own
import and export names (`Layout.ofComp`) and the world-level `accept` function; only the core
semantics `C` is required. `Silmaril.Wasm.Game.Accept.moduleBytesSystem` is the module-only
counterpart. The parser reads `list<u8>`, but the lowering into the IR does not, so only
fixed-arity `accept(tuple<u8, …>)` components reach it (see `componentBytesSystem`).

**Either shape.** `ByteAcceptor.decode` reads bytes as a core module (`decode?`) or, failing
that, as a component. The two binary formats differ in their header's layer field, so at most
one of the decoders is expected to succeed; the module decoder is tried first.

As for modules, bytes that do not decode prove nothing.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Consequence (System)
open Silmaril.Wasm.Component (Comp CoreModule CoreSem)
open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

namespace ComponentAcceptor

variable {M : Type} [CoreModule M] (C : CoreSem M) (L : Layout) (acc : FnName := acceptFn)
  (rej : Option FnName := none) (mode : Mode := .imp)

/-- **The component interpreter**: an IR component under a core semantics and a layout, with its
distinguished functions. -/
def interp : Comp M → ComponentAcceptor := fun c => ofIR C L c acc rej mode

/-- **Components as a consequence system**: `c ⊢ w` iff `interp C L … c` accepts `w`. -/
def compSystem : System (Comp M) (List UInt8) := System.ofInterpreter (interp C L acc rej mode)

/-- **Encoded components as a consequence system**, through any decoder: `b ⊢ w` iff `b`
decodes to a component `c` with `c ⊢ w`. -/
def bytesSystem {B : Type} (decode : B → Option (Comp M)) : System B (List UInt8) :=
  System.ofDecoder decode (interp C L acc rej mode)

/-- The component binary decoder: parse and lower (`parseComponent`), forgetting the error. -/
def decodeBinary (b : ByteArray) : Option (Comp Silmaril.Wasm.Component.Binary.CoreMod) :=
  (Silmaril.Wasm.Component.Binary.parseComponent b).toOption

/-- **Component binaries as a consequence system**, for a core semantics of the lowered core
modules. -/
def binarySystem (C : CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Layout)
    (acc : FnName := acceptFn) (rej : Option FnName := none) (mode : Mode := .imp) :
    System ByteArray (List UInt8) :=
  bytesSystem C L acc rej mode decodeBinary

end ComponentAcceptor

/-! ## Self-describing component interpretation -/

/-- The function a lowered import or export name denotes: the world-level function `⟨"", n⟩`.
Functions of instances keep the flattened name `inst#f` that `Binary.lower` gives them. -/
def fnNameOf (n : String) : FnName := ⟨"", n⟩

/-- **The layout a component names itself**: its imports and exports, by their own names. -/
def Layout.ofComp {M : Type} (c : Comp M) : Layout :=
  ⟨c.imports.map (fnNameOf ·.1), c.exports.map (fnNameOf ·.name)⟩

/-- The component `c` read through its own names, with the `accept` function `acceptFn`
(`accept` at world level), imported by default. -/
def ComponentAcceptor.ofComp {M : Type} [CoreModule M] (C : CoreSem M) (c : Comp M)
    (mode : Mode := .imp) : ComponentAcceptor :=
  ofIR C (Layout.ofComp c) c acceptFn none mode

/-- **Component binaries as a consequence system**: `b ⊢ w` iff `b` is a component binary that
parses and lowers (`parseComponent`) to a component `c` whose world-level `accept` function,
under the core semantics `C`, accepts `w` (imported `accept` called with `w`, or exported
`accept(w)` returning `true`, by `mode`). The layout is the component's own (`Layout.ofComp`), so
the only required parameter is `C`, the semantics of the lowered core modules. Core module binaries and other bytes do not decode and prove nothing.

`w` reaches `accept` as a record/tuple of `u8` (`bytes?`). The component *parser*
(`Binary.parse`) reads `list<u8>`, but the *lowering* into the component IR (`Binary.lower`, which
every IR lowering shares) rejects list types: the IR's value types have no list type and no
memory-based canonical ABI. So a typical `accept(list<u8>)` binary does not decode here and proves
nothing; a fixed-arity `accept(tuple<u8, …>)` (at most 16 flat parameters) does decode. The
reference semantics (`Conformance.decodeRef`) reads list types but has no trace semantics with
imports, so it cannot replace this path. `C` is any core semantics of the lowered modules; the
only one in the library is the loosest, `Silmaril.Project.WasmComponents.topSem`, where every core
module may play any legal play.
-/
def componentBytesSystem (C : CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (mode : Mode := .imp) : System ByteArray (List UInt8) :=
  System.ofDecoder ComponentAcceptor.decodeBinary fun c => ComponentAcceptor.ofComp C c mode

namespace ByteAcceptor

/-- **The interpreter of programs of either shape**: modules through the template `A`
(`ModuleAcceptor.withModule`), components (or any `W`) through `I`. -/
def interp {W : Type} (A : ModuleAcceptor) (I : W → ComponentAcceptor) :
    Silmaril.Wasm.Module ⊕ W → ByteAcceptor :=
  Sum.map A.withModule I

/-- **Programs of either shape as a consequence system.** -/
def programSystem {W : Type} (A : ModuleAcceptor) (I : W → ComponentAcceptor) :
    System (Silmaril.Wasm.Module ⊕ W) (List UInt8) :=
  System.ofInterpreter (interp A I)

/-- Decode bytes as a core module, or else as a component. -/
def decode : ByteArray → Option (Silmaril.Wasm.Module ⊕ Comp Silmaril.Wasm.Component.Binary.CoreMod) :=
  fun b => (Silmaril.Wasm.Binary.Core.decode? b).map .inl <|>
    (ComponentAcceptor.decodeBinary b).map .inr

/-- **Wasm binaries of either shape as a consequence system**: `b ⊢ w` iff `b` decodes as a
module that `A.withModule` reads as accepting `w`, or else as a component that
`ComponentAcceptor.interp C L …` reads as accepting `w`. -/
def bytesSystem (A : ModuleAcceptor) (C : CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Layout) (acc : FnName := acceptFn) (rej : Option FnName := none)
    (mode : Mode := .imp) : System ByteArray (List UInt8) :=
  System.ofDecoder decode (interp A (ComponentAcceptor.interp C L acc rej mode))

end ByteAcceptor

end Silmaril.Wasi.Accept
