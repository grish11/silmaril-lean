module

public import Silmaril.Wasm.Component.Reference.LinkedSessionIR.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs

/-!
# Linked components whose importer also has host imports: definitions

**Scope.** `HLinked2` is `Linked2` (#697 … #746) with host imports. The import-free exporter A
(`exp`, a `Simple`) answers the first `wire.length` imports of the importer B (`imp`, a
`SimpleI`). The remaining imports of B are host imports of the parent component (`host`), passed
through to B in order: import `wire.length + i` of B is host import `i`. `Linked2` is the case
`host = []` (`Linked2.toH`). The shape generalises #697's hand-written `linkedHRef`, which is
`linkedH.toRef` (`HLinkedSession.Thms`).

The **Shape** condition says the component imports of B are the wired ones followed by `host`:
`imp.imports = wiredImports ++ host`, with `wiredImports.length = wire.length`.

## Translations

* `HLinked2.toComp : Comp ImpModule` is the IR. It is a parent with the imports `host`
  (environment functions `0, …, k - 1`, `k = host.length`) and two nested instances: A (through
  `SimpleI.ofSimple`, its exports at `k, …`), and B. B's import `n` is wired to environment
  function `k + wire[n]` for `n < wire.length`, and to host function `n - wire.length`
  otherwise. Its denotation `l.toComp.den C` is a strategy
  `Strategy (sigN k) (sigN imp.exports.length)`: **the host imports are visible import moves on
  the lower interface.**
* `HLinked2.toRef : Core3Component` is the reference translation. It has the host imports
  (`SimpleI.importsDefs host 0`, component functions `0, …, k - 1`), then both children. It
  instantiates A, aliases A's wired exports (functions `k, …, k + wire.length - 1`), and
  instantiates B with them and with the host functions (`importFid`). It then aliases B's
  exports and exports them (function `k + wire.length + i` for export `i`).

## Layout and hypotheses

* `HLinked2.fid l n` is the component function answering import `n` of B in the instantiated
  `l.toRef`: `k + wire[n]` (A's lifted function `wire[n]`, after the `k` host functions) for a
  wired import, host function `n - wire.length` otherwise. `HLinked2.exportMap` is the export
  map of the instantiated `l.toRef` (export `i` at `k + exp.exports.length + i`).
* `HLinked2.WireTy` is `Shape` with the typing of the wired imports (`Linked2.WireTy.ty`).
  `HLinked2.Adequate` is `Linked2.Adequate` with `WireTy` in place of `Linked2.WireTy`.

## Specification and IR plays of sessions

* `HLinked2.ExpRunH P l I π ds π'` takes the component import calls `ds` of B in order. A wired
  call is answered by A's specification, returned (`RetAt`) or trapped (`TrapAt`), with A's Core
  store threaded as in `Linked2.ExpRunT`. A host call (`n = wire.length + i`) is passed through
  with any answer and leaves A's store alone. Constraints on the host's answers belong to the
  reference side (`HostRun`), not to the IR.
* `HLinked2.hostCalls l ds` is the host calls of `ds`, renamed to the host interface
  `sigN host.length`.
* `HLinked2.SessSpec P l Ie Ii u π calls outs hs u' π'` is `Linked2.SessSpec` with
  `ExpRunH` in place of `ExpRunT`. It also records the host calls `hs` of each round.
* `HLinked2.sessMoves l calls outs hs` is the IR play of a session. Each call asks, makes its
  host calls as visible lower moves, and answers its result or a trap (`none`).

## Observations, from reference-machine runs only

* `HLinked2.sessObs P prof l g s₀ calls` is the resumable-session outcomes of `l.toRef` under the
  stateful host `answerHostS P (logG g)`, together with the final host state. `logG g` answers as
  `g` and appends every answered host call `(function, arguments, results)` to a log in the host
  state, so **the host log is observable**. A host call that `g` refuses traps
  (`answerImplS`), and nothing is logged for it.
* `HLinked2.silentObs P prof l calls` is the same sessions under `silentHost P`, a host that
  takes every call (`on_start`) and never resolves it.
* `HLinked2.HostTyped l g`: whenever `g` answers a host import called on reference images of IR
  values, its answer is the reference image of IR values of the import's result types. The
  specification to reference direction assumes it (an ill-typed answer is an `internal` fault of
  the reference machine, not a trap). `HLinked2.silentG` never answers: `HostRun silentG` says
  that every host call is answered by a trap.

**Synchronous lowering: a host that never answers is a trap, not a pending call.** Every
`canon lower` and `canon lift` of the `SimpleI` fragment is synchronous. A host call that is
never resolved leaves no ready thread in the instance, so `canon_lift`'s synchronous loop
traps `cannotBlockSync` (REF `trap_if(not candidates)`). #697 shows this for the fixture
(`linkedH_silent_cannotBlock`, restated for `linkedH.toRef` in `Thms`); for every `HLinked2` with
adequate parts it is `HLinked2.silent_cannotBlock` (`Thms`) for the first call after
instantiation, and `HLinked2.silent_cannotBlock_sess` for any call of a session. A pending observation, where the host diverges and the call stays unresolved,
needs an asynchronous `canon lower` or `canon lift`. It is out of scope and comes later.

**Not covered.** n-ary and nested components wait on the H2 owner's host hiding and `ext` laws
(#207). The parser from bytes to these components, and F6, are pending.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-- **Two components linked, with host imports passed through**: import `n < wire.length` of
the importer `imp` is answered by export `wire[n]` of the import-free exporter `exp`; import
`wire.length + i` is host import `i` of the parent (`host`). -/
structure HLinked2 where
  /-- The exporter. -/
  exp : Simple
  /-- The importer. -/
  imp : SimpleI
  /-- For each wired import of `imp` (the first `wire.length`), the export of `exp` answering
  it. -/
  wire : List Nat
  /-- The host imports of the parent, passed through to the remaining imports of `imp`. -/
  host : Iface

namespace HLinked2

/-- The underlying `Linked2` (the host imports forgotten). -/
abbrev toL2 (l : HLinked2) : Linked2 := ⟨l.exp, l.imp, l.wire⟩

/-- **The shape of the importer's imports**: the wired imports, one per entry of `wire`,
followed by exactly the host imports. -/
def Shape (l : HLinked2) : Prop :=
  l.imp.imports.drop l.wire.length = l.host ∧ l.wire.length ≤ l.imp.imports.length

/-! ## The IR -/

/-- The wiring of the importer's wired imports to the exporter's exports (after the `k` host
imports). -/
def wireArgs (l : HLinked2) : List Impl :=
  l.wire.map fun w => ⟨[], .call (l.host.length + w)⟩

/-- The wiring of the importer's host imports to the parent's imports. -/
def hostArgs (l : HLinked2) : List Impl :=
  l.host.mapIdx fun i _ => ⟨[], .call i⟩

/-- **The IR composition**: a parent component with the host imports, instantiating the
exporter and the importer (wired imports to the exporter, the rest to the host imports), and
exporting the importer's exports. -/
def toComp (l : HLinked2) : Comp ImpModule :=
  .mk l.host [.inst (SimpleI.ofSimple l.exp).toComp [],
      .inst l.imp.toComp (l.wireArgs ++ l.hostArgs)]
    (l.imp.exports.mapIdx fun i x =>
      { name := x.name, ty := x.ty,
        impl := ⟨[], .call (l.host.length + l.exp.exports.length + i)⟩ })

theorem exports_length_toComp (l : HLinked2) :
    l.toComp.exports.length = l.imp.exports.length := by
  simp [toComp]

/-! ## The reference translation -/

/-- The component function of the parent passed to import `n` of the importer: the alias of the
wired export (`k + n`) for a wired import, host function `n - wire.length` otherwise. -/
def importFid (l : HLinked2) (n : Nat) : Nat :=
  if n < l.wire.length then l.host.length + n else n - l.wire.length

/-- **The reference translation**: the host imports, both children, the exporter's instance,
the aliases of its wired exports, the importer's instance (wired imports from the aliases, host
imports from the host functions), the aliases of the importer's exports, and their exports. -/
def toRef (l : HLinked2) : Core3Component :=
  (SimpleI.importsDefs l.host 0).1 ++
    [.component l.exp.toRef, .component l.imp.toRef, .instance_ (.instantiate 0 [])] ++
    (l.wire.map fun w => .alias (.export_ 0 (l.toL2.expName w) .func)) ++
    [.instance_ (.instantiate 1 (l.imp.imports.mapIdx fun n p => (p.1, ⟨.func, l.importFid n⟩)))] ++
    (l.imp.exports.map fun x => .alias (.export_ 1 x.name .func)) ++
    (l.imp.exports.mapIdx fun i x =>
      .export_ { name := x.name } ⟨.func, l.host.length + l.wire.length + i⟩ none)

/-! ## The layout of the instantiated parent -/

/-- **The component function answering import `n` of the importer** in the instantiated
`l.toRef`: the host functions are component functions `0, …, k - 1` (`k = host.length`) and the
exporter's lifted functions follow them, so a wired import `n` is the exporter's lifted function
`k + wire[n]`, and the host import `n` (`n ≥ wire.length`) is host function `n - wire.length`. -/
def fid (l : HLinked2) (n : Nat) : Silmaril.Wasm.Component.Runtime.FuncId :=
  ⟨if n < l.wire.length then l.host.length + l.wire.getD n 0 else n - l.wire.length⟩

/-- **The function exports of the instantiated `l.toRef`**: export `i` of the importer is its
lifted function `i`, after the `k` host functions and the exporter's lifted functions. -/
def exportMap (l : HLinked2) : List (String × Silmaril.Wasm.Component.Runtime.FuncId) :=
  l.imp.exports.mapIdx fun i x => (x.name, ⟨l.host.length + l.exp.exports.length + i⟩)

/-! ## Hypotheses -/

/-- **The wiring and the host imports are well typed**: the importer's imports are the wired
ones followed by exactly the host imports (`Shape`: names and types of the host imports are
those of the importer's imports `wire.length, …`), and the export `wire[n]` answering the
wired import `n` is an export of the exporter of the import's type (`Linked2.WireTy.ty`). -/
structure WireTy (l : HLinked2) : Prop where
  shape : l.Shape
  ty : ∀ (k w : Nat), l.wire[k]? = some w →
    ∃ x : SimpleExport, l.exp.exports[w]? = some x ∧
      (l.imp.imports[k]?).map (fun p : String × FuncTy => p.2) = some x.ty

/-- **The adequacy hypotheses of a linked component with host imports**: those of
`Linked2.Adequate`, with the wiring condition `Linked2.WireTy` (one wired export per import)
replaced by `HLinked2.WireTy` (one wired export per wired import, the remaining imports being
the host imports). -/
structure Adequate (l : HLinked2) : Prop where
  expGood : l.exp.Good
  expInst : l.exp.Inst
  impGood : l.imp.Good
  impInst : l.imp.Inst
  impArity : l.imp.Arity
  impFloatFree : l.imp.FloatFree
  wireTy : l.WireTy
  namesOk : l.toL2.NamesOk
  wireNodup : l.toL2.WireNodup
  splitOk : l.toL2.SplitOk

end HLinked2

/-- A `Linked2` as an `HLinked2` without host imports. -/
def Linked2.toH (l : Linked2) : HLinked2 := ⟨l.exp, l.imp, l.wire, []⟩

namespace HLinked2

/-! ## Specification of sessions -/

section Spec

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-- **Import calls of the importer, wired calls answered by the exporter, host calls passed
through**: a wired call (`wire[n] = w`) is a returned (`RetAt`) or trapped (`TrapAt`, answered
`none`) call of export `w` from the exporter's current store, threading it; a host call (import
`wire.length + i`) has any answer and leaves the exporter's store unchanged. -/
inductive ExpRunH (P : Profile) (l : HLinked2) (I : ScalarInstance) :
    Store Nat → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → Store Nat → Prop
  | nil (s : Store Nat) : ExpRunH P l I s [] s
  | ret {s s₁ s' : Store Nat} {n : Fin l.imp.imports.length} {ws us : List IVal}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (w : Fin l.exp.exports.length) :
      l.wire[n.val]? = some w.val → RetAt P l.exp I l.exp.exports[w] ws s us s₁ →
      ExpRunH P l I s₁ ds s' → ExpRunH P l I s (⟨(n, .vals ws), some (.vals us)⟩ :: ds) s'
  | trap {s s₁ s' : Store Nat} {n : Fin l.imp.imports.length} {ws : List IVal}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (w : Fin l.exp.exports.length) :
      l.wire[n.val]? = some w.val → TrapAt P l.exp I l.exp.exports[w] ws s s₁ →
      ExpRunH P l I s₁ ds s' → ExpRunH P l I s (⟨(n, .vals ws), none⟩ :: ds) s'
  | host {s s' : Store Nat} {n : Fin l.imp.imports.length} {p : Payload} {R : Option Payload}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (i : Fin l.host.length) :
      n.val = l.wire.length + i.val → ExpRunH P l I s ds s' →
      ExpRunH P l I s (⟨(n, p), R⟩ :: ds) s'

/-- A component import call of the importer as a host call (`none` for a wired call). -/
def hostCall? (l : HLinked2) (d : Σ _ : (sigN l.imp.imports.length).Op, Option Payload) :
    Option (Σ _ : (sigN l.host.length).Op, Option Payload) :=
  if h : l.wire.length ≤ d.1.1.val ∧ d.1.1.val - l.wire.length < l.host.length then
    some ⟨(⟨d.1.1.val - l.wire.length, h.2⟩, d.1.2), d.2⟩
  else none

/-- The host calls among the importer's component import calls, at the host interface. -/
def hostCalls (l : HLinked2) (ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)) :
    List (Σ _ : (sigN l.host.length).Op, Option Payload) :=
  ds.filterMap l.hostCall?

/-- **The specification of a session**: each call is a well-formed round of the importer's core
instance from its current store, whose component import calls are an `ExpRunH` segment from the
exporter's current store, whose lifted answer is the outcome, and whose host calls are
recorded. -/
inductive SessSpec (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance) :
    Store Nat → Store Nat → List (Fin l.imp.exports.length × List IVal) →
    List (Option (List IVal)) → List (List (Σ _ : (sigN l.host.length).Op, Option Payload)) →
    Store Nat → Store Nat → Prop
  | nil (u π : Store Nat) : SessSpec P l Ie Ii u π [] [] [] u π
  | round {u π u₁ π₁ u' π' : Store Nat} {cs : List (Fin l.imp.exports.length × List IVal)}
      {outs : List (Option (List IVal))}
      {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
      {o : Option (List IVal)} (d : Linked2.SessRound l.toL2 Ii) :
      d.Ok → Ii.Path P (.idle u) d.instMoves (.idle u₁) → ExpRunH P l Ie π d.dss.flatten π₁ →
      d.ans = o.map .vals → SessSpec P l Ie Ii u₁ π₁ cs outs hs u' π' →
      SessSpec P l Ie Ii u π ((d.j, d.vs) :: cs) (o :: outs)
        (l.hostCalls d.dss.flatten :: hs) u' π'

end Spec

/-- **The IR play of a session**: each call `(j, vs)` asks, makes its host calls (visible
import moves), and answers its results or a trap (`none`). -/
def sessMoves (l : HLinked2) :
    List (Fin l.imp.exports.length × List IVal) → List (Option (List IVal)) →
    List (List (Σ _ : (sigN l.host.length).Op, Option Payload)) →
    List (Silmaril.Games.Move (sigN l.host.length) (sigN l.toComp.exports.length))
  | (j, vs) :: cs, o :: os, h :: hs =>
    .inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) ::
      (callMoves h ++ .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs))
        (o.map .vals)) :: sessMoves l cs os hs)
  | _, _, _ => []

/-! ## Observations on the reference machine -/

section Obs

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Numerics (Profile)

/-- A host call of the log: the host function, its arguments and its results. -/
abbrev HostEvent : Type := HostFuncId × List RVal × List RVal

/-- **A logging host**: answers as `g`, and appends each answered call to the log. -/
def logG {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) :
    σ × List HostEvent → HostFuncId → List RVal → Option (List RVal × (σ × List HostEvent)) :=
  fun s fn args => (g s.1 fn args).map fun r => (r.1, (r.2, s.2 ++ [(fn, args, r.1)]))

/-- **A typed host**: whenever `g` answers host import `i` called on the reference image of IR
values, its answer is the reference image of IR values of the import's result types. This is
needed: an ill-typed answer is not a trap of the reference machine but the `internal` fault
`lower_flat: value does not match type`, while the specification traps (`Thms`). -/
def HostTyped (l : HLinked2) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) : Prop :=
  ∀ (s : σ) (i : Nat) (hi : i < l.host.length) (ws : List IVal) (rs : List RVal) (s' : σ),
    g s ⟨i⟩ (ws.map toRefVal) = some (rs, s') →
      ∃ us : List IVal, rs = us.map toRefVal ∧ ValTy.checkList l.host[i].2.results us = true

/-- **The answering function of a host that never answers** (`HostRun silentG` holds of host
calls all answered by a trap). -/
def silentG {σ : Type} : σ → HostFuncId → List RVal → Option (List RVal × σ) :=
  fun _ _ _ => none

/-- The reference calls of a session: the importer's export names, on the reference images of
the IR arguments. -/
def refCalls (l : HLinked2) (calls : List (Fin l.imp.exports.length × List IVal)) :
    List (String × List RVal) :=
  calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)

/-- **Session observations with the host log**: the resumable-session outcomes of `l.toRef`
(instantiated from the host functions of `l.host`) for the calls `calls`, under the logging
host of `g` from `s₀` and the empty log; with the final host state and the log of host calls. -/
noncomputable def sessObs (P : Profile) (prof : ProfileKind) (l : HLinked2) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) :
    Set (List (Option (List RVal)) × (σ × List HostEvent)) :=
  LinkedSession.sessRunBehaviours prof (answerHostS P (logG g)) (s₀, []) l.toRef l.host
    (l.refCalls calls)

variable {E : Engine} {σ : Type}

/-- **A host that never answers**: each host function takes its arguments (`on_start`) and
returns without resolving the call. -/
def silentImpl : HostImpl E σ :=
  HostImpl.ofFns fun _ c => do
    let _ ← callVals (.onStart c)
    pure (.cancel .none)

/-- The reference host that never answers (no host waitable is ever ready). -/
noncomputable def silentHost (P : Profile) : Host (core3P P) σ :=
  { hr := fun _ _ => false, impl := silentImpl }

/-- **Session observations under a host that never answers**: the resumable-session outcomes
of `l.toRef`, with the final host state. On this synchronous fragment an unanswered host call is
expected to be a `cannotBlockSync` trap (the module docstring), not a pending call. -/
noncomputable def silentObs (P : Profile) (prof : ProfileKind) (l : HLinked2) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) :
    Set (List (Option (List RVal)) × σ) :=
  LinkedSession.sessRunBehaviours prof (silentHost P) s₀ l.toRef l.host (l.refCalls calls)

end Obs

end HLinked2

namespace LinkedSession

/-- **#697's host-import fixture as an `HLinked2`**: A answers B''s `set` and `get`; B''s third
import `h` is the parent's host import. -/
def linkedH : HLinked2 := ⟨setGetS, pokePeekPingI, [0, 1], hostIface⟩

end LinkedSession

end Silmaril.Wasm.Component.Reference
