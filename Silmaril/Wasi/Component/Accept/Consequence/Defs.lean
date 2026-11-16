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
its lowering is partial and unverified, and no core semantics `CoreSem CoreMod` is fixed in the
library, so `C` is a parameter. `bytesSystem` takes any decoder.

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
