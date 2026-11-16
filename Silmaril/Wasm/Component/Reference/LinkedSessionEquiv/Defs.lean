module

public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs

/-!
# The resumable-session equivalence of linked components: definitions

**Scope.** `Linked2` only: the import-free exporter A (`l.exp`, a `Simple`) answering every
import of the importer B (`l.imp`, a `SimpleI`) through the canonical ABI (`Link.Defs`). The
reference component is `l.toRef`; its sessions are the resumable sessions of `SessionAdequacy`
(`SessCalls`, a trapped call resuming from `resumeCfg`; a modelling choice, REF itself locks the
store down after a trap), observed through `Linked2.sessObs` (`LinkedSessionRef.Defs`).

* `Linked2.RefSessEquiv P prof l l'`: defined on the reference machine only. The importers have
  the same number of exports with the same types, and for every typed sequence of calls the
  resumable-session outcomes of `l.toRef` and `l'.toRef` are the same, under every host
  (`linkHost impl`, any host state). `l.toRef` imports nothing, so the host is never called.
  Export names are not compared: the IR calls exports by position.
* `Linked2.SameTypes l l'`: the importers' exports have the same types, in order.
* `Linked2.typedQ l q`: whether a question `q` of the untyped export interface `sigU` is a typed
  call of the linked component (export `j` of the importer, on IR values of its parameter
  types), and which. The other questions (an index out of range, a flat payload, or values of
  the wrong types) are the **ill-typed calls**.

**Hypotheses** (`Linked2.Adequate`, the hypotheses of `Linked2.sound`): exporter `Good` and
`Inst`; importer `Good`, `Inst`, `Arity` and `FloatFree`; `WireTy`, `NamesOk`, `WireNodup`;
`SplitOk`.

**Host observations.** Within `Linked2` every import of B is wired to A, so `l.toRef` has no
host imports and `linkHost impl` is never called: `RefSessEquiv` quantifies over hosts only to be
stated on reference runs without fixing one. A parent that also passes host imports to B (as
`linkedHRef`) lets B call the host where `SimpleI` allows it; those observations are not covered
here.

**Not covered.** Divergence (`SessCalls` records terminating outcomes only and `Comp.den` has
finite plays); productive (infinite) linked executions, the next step through the H2 owner's
`mem_inf_linkS_iff_of_det` (`Games.Abstract.SessionLink`); the parser from bytes to these
components, and F6, are pending.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

/-- Calls of the exports of `l`, as calls of the exports of `l'` with the same indices. -/
def castCalls {l l' : Linked2} (h : l.imp.exports.length = l'.imp.exports.length)
    (calls : List (Fin l.imp.exports.length × List IVal)) :
    List (Fin l'.imp.exports.length × List IVal) :=
  calls.map fun q => (Fin.cast h q.1, q.2)

/-- The same export types of the importers, in order. -/
def SameTypes (l l' : Linked2) : Prop := l.imp.exports.map (·.ty) = l'.imp.exports.map (·.ty)

/-- **The typed call of a question** of the untyped export interface, if it is one: export `j`
of the importer on IR values of its parameter types. -/
def typedQ (l : Linked2) : Nat × Payload → Option (Fin l.imp.exports.length × List IVal)
  | (j, .vals vs) =>
    if h : j < l.imp.exports.length then
      if ValTy.checkList l.imp.exports[j].ty.params vs then some (⟨j, h⟩, vs) else none
    else none
  | (_, .flat _) => none

/-- **The resumable-session equivalence of linked components**, on the reference machine only:
the same export types, and for every typed sequence of calls the same resumable-session outcomes
of `l.toRef` and `l'.toRef`, under every host. -/
structure RefSessEquiv (P : Profile) (prof : ProfileKind) (l l' : Linked2) : Prop where
  len : l.imp.exports.length = l'.imp.exports.length
  ty : ∀ j : Fin l.imp.exports.length, l'.imp.exports[Fin.cast len j].ty = l.imp.exports[j].ty
  obs : ∀ calls : List (Fin l.imp.exports.length × List IVal), SimpleI.TypedCalls l.imp calls →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      sessObs prof l impl h₀ calls = sessObs prof l' impl h₀ (castCalls len calls)

end Linked2

end Silmaril.Wasm.Component.Reference

/-! ## A witness: the exporter's exports renamed -/

namespace Silmaril.Wasm.Component.Reference.LinkedSession

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- The exporter A with its component exports renamed: `put: func()` and `got: func() -> u32`,
lifted from the same module A (`set` and `get` stay the core export names). -/
def putGotS : Simple := ⟨setGetS.mod, [⟨"put", unitTy, 0⟩, ⟨"got", u32Ty, 1⟩]⟩

/-- **`linkedC` with the renamed exporter**: B's imports `set` and `get` are answered by A's
exports `put` and `got`. Its reference component `linkedR.toRef` differs from `linkedC.toRef`
(the exporter's exports, and the parent's aliases of them, have other names). -/
def linkedR : Linked2 := ⟨putGotS, pokePeekI, [0, 1]⟩

end Silmaril.Wasm.Component.Reference.LinkedSession
