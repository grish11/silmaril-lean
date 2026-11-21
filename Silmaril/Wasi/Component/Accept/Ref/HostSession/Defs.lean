module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs

/-! # Acceptance through a host import, REF sessions against IR plays: definitions

**Scope.** The fragment is `Reference.HLinked2` (#758 … #782): a core module with host imports
(`SimpleI`: the module's import `k` is the `canon lower` of component import `k`, at
scalar/record/variant types, no linear memory, no start function, exports `canon lift`ed),
whose first `wire.length` imports may be answered by an import-free exporter (`Simple`); the
remaining imports are the parent's host imports. The `accept` function is one of these host
imports, `a : Fin l.host.length`. The `tuple<u8, u8>` acceptor shape is the case of a host
import `accept: func(record<u8, u8>)` (the IR's tuples are records).

Acceptance is read through the **logging host** of #782 (`HLinked2.logG g`): the host answers
as `g`, and every answered host call `(function, arguments, results)` is appended to a log in
the host state. Both readings count an `accept` call by its arguments, read as bytes the way
each side reads them (`bytesOf?` on REF values, `args1 bytes?` on IR values; they agree,
`bytesOf?_toRefVal`).

* `HLinked2.SessAcceptedRef P prof l g s₀ a w`: some finite session of typed calls of `l.toRef`
  on the reference machine over `core3P P`, under the logging host of `g` from `s₀`
  (`HLinked2.sessObs`), logs a call of host function `a` whose arguments carry `w`.
* `HLinked2.SessAcceptedIR P l g s₀ a w`: some session play of the IR `l.toComp.den (impSem P)`
  (`HLinked2.sessMoves`, typed calls, one outcome and one list of host calls per call), whose
  host calls are answered as the logging host of `g` answers them from `s₀` (`HostRun`), has an
  answered host call of import `a` whose arguments carry `w`.
* `posBytesLang σ a`: the bytes carried by some question to import position `a` in some play
  of a positional strategy `σ : Strategy (sigN n) (sigN k)`, whatever the environment answers.
  It is the positional counterpart of `bytesLang` (which reads the named view
  `Layout.compModel`).

**Why the host's answers are part of the IR side.** The IR's plays let the environment answer
an import question with anything, a trap included, and a component's later calls may depend on
that answer: after a trapped call the session resumes from the store the trap left. A host that
always answers `accept` never produces those plays. So the IR language over all plays
(`posBytesLang`, and likewise `bytesLang` of the named view) can be strictly larger than what a
fixed host observes on REF; the equality holds once the IR plays are restricted to the answers
of the same host (`SessAcceptedIR`). `Thms` proves the equality and the inclusion into
`posBytesLang`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-- **An answered call of import `a` carrying `w`**: the component import call `d` asks import
`a` on IR values `ws` that carry the bytes `w` (`args1 bytes?`) and is answered with IR values
(not a trap). -/
def AnsweredCarries {n : Nat} (a : Fin n) (w : List UInt8)
    (d : Σ _ : (sigN n).Op, Option Payload) : Prop :=
  ∃ ws us : List IVal, d = ⟨(a, .vals ws), some (.vals us)⟩ ∧ args1 bytes? ws = some w

/-- **The bytes questions to import position `a` carry**, in the plays of a positional strategy:
`w` is accepted when some play asks import `a` on component values carrying `w`, whatever the
environment answers. -/
def posBytesLang {n k : Nat} (σ : Strategy (sigN n) (sigN k)) (a : Fin n) : Set (List UInt8) :=
  {w | ∃ p ∈ σ, ∃ ws : List IVal, (.inl (.ask (a, .vals ws)) : Move (sigN n) (sigN k)) ∈ p ∧ args1 bytes? ws = some w}

namespace HLinked2

variable (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (l : HLinked2) {σ : Type}
  (g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId → List RVal → Option (List RVal × σ))
  (s₀ : σ) (a : Fin l.host.length) (w : List UInt8)

/-- **Session acceptance on the reference machine**: some session of typed calls of `l.toRef`
over `core3P P`, under the logging host of `g` from `s₀`, logs a call of host function `a` on
arguments carrying `w` (`bytesOf?`). -/
def SessAcceptedRef : Prop :=
  ∃ calls : List (Fin l.imp.exports.length × List IVal), SimpleI.TypedCalls l.imp calls ∧
    ∃ p ∈ HLinked2.sessObs P prof l g s₀ calls,
      ∃ ev ∈ p.2.2, ev.1 = ⟨a.val⟩ ∧ bytesOf? ev.2.1 = some w

/-- **Session acceptance in the IR, at the host's answers**: some session play of
`l.toComp.den (impSem P)` of typed calls, whose host calls the logging host of `g` answers from
`s₀`, has an answered call of host import `a` carrying `w`. -/
def SessAcceptedIR : Prop :=
  ∃ calls : List (Fin l.imp.exports.length × List IVal), SimpleI.TypedCalls l.imp calls ∧
    ∃ (outs : List (Option (List IVal)))
      (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload)))
      (st' : σ × List HLinked2.HostEvent),
      calls.length = outs.length ∧ calls.length = hs.length ∧
      l.sessMoves calls outs hs ∈ l.toComp.den (impSem P) ∧
      HostRun (HLinked2.logG g) (s₀, []) hs.flatten st' ∧
      ∃ d ∈ hs.flatten, AnsweredCarries a w d

end HLinked2

end Silmaril.Wasi.Accept.Ref
