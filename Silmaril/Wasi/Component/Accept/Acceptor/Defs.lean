module

public import Silmaril.Wasi.Component.Accept.Reject.Defs
public import Silmaril.Wasi.Component.Accept.Bounds.Defs
public import Silmaril.Wasm.Game.Accept.Acceptor.Defs

/-! # Component acceptors, and acceptors of either shape

`ComponentAcceptor` packages a component (a model of a world) with:

* its distinguished `accept` function, read as an imported `accept(list<u8>)` or as an
  exported `accept(list<u8>) -> bool` (`Mode`);
* an optional `reject` function, read in the same mode: an import that is never called, or
  an export that never returns `false`.

Its languages are `lang`, `neverRejectedLang` and `strictLang`, as for `ModuleAcceptor`.
`ComponentAcceptor.ofIR C L c` is the acceptor of an IR component under a layout.

`ByteAcceptor` is the sum of the two shapes, with the language of each. Module and component
acceptors are compared by language in one carrier; the sum's inclusions preserve and
reflect languages. All three are CSLib `Acceptor`s over bytes.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Comp CoreModule)
open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

/-- How the distinguished functions are read. -/
inductive Mode where
  /-- Imported: `accept(list<u8>)` is called; `reject(list<u8>)` is never called. -/
  | imp
  /-- Exported: `accept(list<u8>) -> bool` may return `true`; `reject(list<u8>) -> bool`
  never returns `false`. -/
  | exp
  deriving DecidableEq, Repr

/-- **A component with distinguished `accept` and `reject` functions.** -/
structure ComponentAcceptor where
  /-- The imports of its world. -/
  I : Set FnName
  /-- The exports of its world. -/
  X : Set FnName
  /-- The component. -/
  model : Strategy (nsig I) (nsig X)
  /-- The accepting function. -/
  accept : FnName := acceptFn
  /-- The rejecting function, if any. -/
  reject : Option FnName := none
  /-- Imported or exported functions. -/
  mode : Mode := .imp

namespace ComponentAcceptor

variable (A : ComponentAcceptor)

/-- The bytes accepted by some play. -/
def lang : ByteLang :=
  match A.mode with
  | .imp => bytesLang A.model A.accept
  | .exp => exportBytesLang A.model A.accept

/-- The bytes no play rejects (every string, without a reject function). -/
def neverRejectedLang : ByteLang :=
  match A.reject, A.mode with
  | none, _ => ⊤
  | some r, .imp => neverCalled A.model r (args1 bytes?)
  | some r, .exp => neverFalse A.model r (args1 bytes?)

/-- Accepted by some play and rejected by none. -/
def strictLang : ByteLang := A.lang ⊓ A.neverRejectedLang

/-- The acceptor of an IR component under a layout. -/
def ofIR {M : Type} [CoreModule M] (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout)
    (c : Comp M) (accept : FnName := acceptFn) (reject : Option FnName := none)
    (mode : Mode := .imp) : ComponentAcceptor :=
  ⟨_, _, L.compModel C c, accept, reject, mode⟩

instance : Cslib.Automata.Acceptor ComponentAcceptor UInt8 := ⟨fun A w => w ∈ A.lang⟩

end ComponentAcceptor

/-- **Byte acceptors of either shape**: a core module or a component. -/
abbrev ByteAcceptor : Type 1 := ModuleAcceptor ⊕ ComponentAcceptor

namespace ByteAcceptor

/-- The language of an acceptor of either shape. -/
def lang : ByteAcceptor → ByteLang := Sum.elim ModuleAcceptor.lang ComponentAcceptor.lang

instance : Cslib.Automata.Acceptor ByteAcceptor UInt8 := ⟨fun A w => w ∈ A.lang⟩

end ByteAcceptor

/-- A module acceptor and a component acceptor (imported mode) **in canonical-ABI
correspondence**: the component's `accept` lists are the module's `accept` segments, read
at the module's address width. -/
def CanonPair (A : ModuleAcceptor) (B : ComponentAcceptor) : Prop :=
  B.mode = .imp ∧
    CanonLowerAcceptBy (Silmaril.Wasm.Game.Accept.segmentDecoder A.addr)
      (Silmaril.Wasm.Game.Accept.Callouts A.profile A.envs A.memIdx A.module) A.accept
      B.model B.accept

end Silmaril.Wasi.Accept
