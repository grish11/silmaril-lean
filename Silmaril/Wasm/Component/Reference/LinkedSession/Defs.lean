module

public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs
public import Silmaril.Wasm.Component.Reference.Link.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs

/-!
# A bounded linked fixture for resumable sessions: definitions

`SessionAdequacy`, `SessionDiv`, `SessionStrat` and `SessionObs` cover `Simple` components only:
one core module, no imports. This module defines a **concrete** reference fixture with two core
modules, an internal call between them whose callee traps, and (in a variant) a host import. It
is a fixture, not a general linked adequacy theorem: the general composition adequacy waits on
the composition closure of `DStrategy` (asked on #207).

## The fixture `linkedC`

* module A (`setGetCore`, the exporter `setGetS`) has a mutable global `g` (initially `0`) and
  exports `set : () -> ()`, which writes `g := 1` and then executes `unreachable` (the callee
  trap), and `get : () -> i32`, which returns `g`;
* module B (`pokePeekCore`, the importer `pokePeekI`) imports A's `set` and `get` and exports
  `poke : () -> ()`, which calls `set`, and `peek : () -> i32`, which calls `get`;
* the component `linkedC : Linked2` exports B's `poke` and `peek` (`peek : func() -> u32`).

Deviation from a single component holding both core modules side by side: the link is the
existing component-level link `Linked2` (the shape of the litmus `dblFwdL`). A and B are nested
components, A's `set` and `get` are `canon lift`ed and B imports them through `canon lower`, so
B's core call of `set` is a cross-instance call of the reference machine (lower, lift, A's core
code), and A's trap aborts it from inside the callee. A direct core-to-core import would be an
ordinary Wasm call inside the shared core store, invisible to the component machine, and the
IR side has no `Linked2`-style infrastructure for it.

## The variant with a host import, `linkedHRef`

`Linked2` composes import-free parents only, so the variant is written as a reference
component directly (`linkedHRef`, reference side only): the parent imports `h : func()` and
passes it to B' (`pokePeekPingI`, B with a third import `h` and a third export `ping`, which
calls `h`). The host import is a real observation here, not a vacuous one:

* `countG`, `embCount`: a host whose function counts its calls in the host state (`Nat`), so
  the number of host callouts of a session is read off the final host state;
* `silentImpl`, `embSilent`: a host whose function takes the call (`on_start`) and never
  resolves it. On this synchronous fixture the reference machine does **not** report a pending
  call (a deadlock with the call unresolved): `ping`'s synchronous `canon lower` waits, no
  thread of the instance is ready, and `canon_lift`'s synchronous loop traps `cannotBlockSync`
  (REF `trap_if(not candidates)`; `Thms`). A pending, host-divergent observation needs an
  asynchronous lift or lower, outside the `SimpleI` fragment.

## Observations, from reference-machine runs only

* `SessRun`: `SessCalls` (resume after a trap from `resumeCfg`) with its final configuration,
  so that the host state at the end is observable;
* `sessRunBehaviours`: instantiate from the host functions' store, run the named calls as a
  resumable session; the outcomes and the final host state;
* `runSess`, `sessSummary`, `callTraps`: executable drivers (`Embedder.callTop`), checked by
  `decide +kernel` and read back through `callTop_sound`.

The fixtures run over `core3 neverFail` with the first-alternative oracle (`first`), as the
earlier linked litmus runs do; other profiles are not covered.

Pending: the parser from bytes to these components, and F6.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.LinkedSession

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-! ## The core modules -/

/-- The recursion groups `[] -> []` (type `0`) and `[] -> [i32]` (type `1`). -/
def unitI32Types : List Silmaril.Wasm.RecType :=
  [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]

/-- Module A: `(global (mut i32) (i32.const 0))
(func (type 0) i32.const 1 global.set 0 unreachable) (func (type 1) global.get 0)
(export "set" (func 0)) (export "get" (func 1))`. -/
def setGetCore : Silmaril.Wasm.Module where
  types := unitI32Types
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 1, .globalSet ⟨0⟩, .unreachable]⟩,
    ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"set", .func ⟨0⟩⟩, ⟨"get", .func ⟨1⟩⟩]

/-- Module B: `(import "env" "set" (func (type 0))) (import "env" "get" (func (type 1)))
(func (type 0) call 0) (func (type 1) call 1) (export "poke" (func 2)) (export "peek" (func 3))`. -/
def pokePeekCore : Silmaril.Wasm.Module where
  types := unitI32Types
  imports := [⟨"env", "set", .func ⟨0⟩⟩, ⟨"env", "get", .func ⟨1⟩⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩, ⟨⟨1⟩, [], [.call ⟨1⟩]⟩]
  exports := [⟨"poke", .func ⟨2⟩⟩, ⟨"peek", .func ⟨3⟩⟩]

/-- Module B': B with a third import `env.h` and a third export `ping`, which calls it. -/
def pokePeekPingCore : Silmaril.Wasm.Module where
  types := unitI32Types
  imports := [⟨"env", "set", .func ⟨0⟩⟩, ⟨"env", "get", .func ⟨1⟩⟩, ⟨"env", "h", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩, ⟨⟨1⟩, [], [.call ⟨1⟩]⟩, ⟨⟨0⟩, [], [.call ⟨2⟩]⟩]
  exports := [⟨"poke", .func ⟨3⟩⟩, ⟨"peek", .func ⟨4⟩⟩, ⟨"ping", .func ⟨5⟩⟩]

/-! ## The components -/

/-- The flat type `[] -> []`. -/
abbrev unitFlat : CoreFuncTy := ⟨[], []⟩

/-- The flat type `[] -> [i32]`. -/
abbrev i32Flat : CoreFuncTy := ⟨[], [.int .i32]⟩

/-- `func()`. -/
abbrev unitTy : FuncTy := ⟨[], []⟩

/-- `func() -> u32`. -/
abbrev u32Ty : FuncTy := ⟨[], [.u32]⟩

/-- The exporter A: `set: func()` and `get: func() -> u32`, lifted from module A. -/
def setGetS : Simple :=
  ⟨⟨setGetCore, [("set", unitFlat), ("get", i32Flat)]⟩,
    [⟨"set", unitTy, 0⟩, ⟨"get", u32Ty, 1⟩]⟩

/-- The importer B: imports `set: func()` and `get: func() -> u32`, lowered into module B, and
exports `poke: func()` and `peek: func() -> u32`. -/
def pokePeekI : SimpleI :=
  ⟨⟨pokePeekCore, [("set", unitFlat), ("get", i32Flat)], [("poke", unitFlat), ("peek", i32Flat)]⟩,
    [("set", unitTy), ("get", u32Ty)], [⟨"poke", unitTy, 0⟩, ⟨"peek", u32Ty, 1⟩]⟩

/-- **The linked fixture**: A answers B's imports `set` and `get` (A's exports `0` and `1`);
the component exports B's `poke` and `peek`. -/
def linkedC : Linked2 := ⟨setGetS, pokePeekI, [0, 1]⟩

/-- The importer B': B with a third import `h: func()` and a third export `ping: func()`. -/
def pokePeekPingI : SimpleI :=
  ⟨⟨pokePeekPingCore, [("set", unitFlat), ("get", i32Flat), ("h", unitFlat)],
      [("poke", unitFlat), ("peek", i32Flat), ("ping", unitFlat)]⟩,
    [("set", unitTy), ("get", u32Ty), ("h", unitTy)],
    [⟨"poke", unitTy, 0⟩, ⟨"peek", u32Ty, 1⟩, ⟨"ping", unitTy, 2⟩]⟩

/-- The component imports of the variant: `h: func()`. -/
def hostIface : Iface := [("h", unitTy)]

/-- **The variant with a host import** (a reference component): the parent imports `h`
(component function `0`), instantiates A, aliases A's `set` and `get` (functions `1`, `2`),
instantiates B' with them and with `h`, aliases B''s `poke`, `peek` and `ping` (functions
`3`, `4`, `5`) and exports them. -/
def linkedHRef : Core3Component :=
  (SimpleI.importsDefs hostIface 0).1 ++
    [.component setGetS.toRef, .component pokePeekPingI.toRef, .instance_ (.instantiate 0 []),
     .alias (.export_ 0 "set" .func), .alias (.export_ 0 "get" .func),
     .instance_ (.instantiate 1 [("set", ⟨.func, 1⟩), ("get", ⟨.func, 2⟩), ("h", ⟨.func, 0⟩)]),
     .alias (.export_ 1 "poke" .func), .alias (.export_ 1 "peek" .func),
     .alias (.export_ 1 "ping" .func),
     .export_ { name := "poke" } ⟨.func, 3⟩ none, .export_ { name := "peek" } ⟨.func, 4⟩ none,
     .export_ { name := "ping" } ⟨.func, 5⟩ none]

/-! ## Session observations on the reference machine -/

section Session

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- **A resumable session with its final configuration**: `SessCalls` (a resolved call
continues from the configuration it ends in, a trapped call resumes from `resumeCfg`), ending
in `m'`. -/
inductive SessRun (prof : ProfileKind) (h : Host E σ) :
    Machine.Config E σ → Nat → List (FuncId × List Val) → List (Option (List Val)) →
    Machine.Config E σ → Prop where
  | nil (m : Machine.Config E σ) (k : Nat) : SessRun prof h m k [] [] m
  | ret {m m₁ m' : Machine.Config E σ} {k : Nat} {f : FuncId} {args rs : List Val}
      {cs : List (FuncId × List Val)} {outs : List (Option (List Val))} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ (.resolved (some rs)) →
      SessRun prof h m₁ (k + 1) cs outs m' →
      SessRun prof h m k ((f, args) :: cs) (some rs :: outs) m'
  | trap {m m₁ m' : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List Val}
      {cs : List (FuncId × List Val)} {outs : List (Option (List Val))} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ .trap →
      SessRun prof h (resumeCfg m m₁) (k + 1) cs outs m' →
      SessRun prof h m k ((f, args) :: cs) (none :: outs) m'

/-- The configuration of the host functions of the imports `ims` (`hostFuncs`), host state
`σ0`, the host in control. -/
def hostConfig (ims : Iface) (σ0 : σ) : Machine.Config E σ :=
  Machine.Config.init (hostFuncs 0 ims CStore.empty) σ0

/-- **Session outcomes with the final host state**: instantiate `c` from the host functions'
store (import `k` bound to host function `k`), then run the exports named in `calls` as a
resumable session; the outcomes and the host state at the end. -/
def sessRunBehaviours (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (ims : Iface) (calls : List (String × List Val)) : Set (List (Option (List Val)) × σ) :=
  {p | ∃ m₀ inst es fs m',
    InstResult.instance m₀ inst es ∈ instBehaviours prof h (hostConfig ims σ0) c (importArgs ims) ∧
    calls.mapM (fun q => es.lookup q.1) = some fs ∧
    SessRun prof h m₀ 0 (fs.zip (calls.map Prod.snd)) p.1 m' ∧ p.2 = m'.host}

/-! ## Executable drivers -/

/-- **A resumable session, executed**: each call by `Embedder.callTop` (at most `fuel` steps),
classified by `callOutcome?`; a trapped call resumes from `resumeCfg`. `none` when a call is
unclassified, cancelled or deadlocked. -/
def runSess (emb : Embedder E σ) (o : Oracle E) (fuel : Nat) :
    Machine.Config E σ → Nat → List (FuncId × List Val) →
    Option (List (Option (List Val)) × Machine.Config E σ)
  | m, _, [] => some ([], m)
  | m, k, (f, args) :: cs =>
    match emb.callTop o fuel ⟨k⟩ f args m with
    | none => none
    | some r =>
      match callOutcome? ⟨k⟩ r with
      | some (.resolved (some rs)) =>
        (runSess emb o fuel r.config (k + 1) cs).map fun p => (some rs :: p.1, p.2)
      | some .trap =>
        (runSess emb o fuel (resumeCfg m r.config) (k + 1) cs).map fun p => (none :: p.1, p.2)
      | _ => none

/-- Instantiation from the host functions' store, then the session of the named calls,
executed: the outcomes and the final host state. -/
def sessSummary (emb : Embedder E σ) (o : Oracle E) (fuel : Nat) (c : CompAst E.Module)
    (ims : Iface) (σ0 : σ) (calls : List (String × List Val)) :
    Option (List (Option (List Val)) × σ) :=
  (emb.instantiateRun o fuel c (importArgs ims) (hostConfig ims σ0)).bind fun (r, _, es) =>
    (calls.mapM fun q => es.lookup q.1).bind fun fs =>
      (runSess emb o fuel r.config 0 (fs.zip (calls.map Prod.snd))).map fun p => (p.1, p.2.host)

/-- Instantiation from the host functions' store, then top-level call `0` of the export `name`
on `args`, executed: the trap reasons of the labels of the call's run (`none` when the
instantiation or the call does not run). -/
def callTraps (emb : Embedder E σ) (o : Oracle E) (fuel : Nat) (c : CompAst E.Module)
    (ims : Iface) (σ0 : σ) (name : String) (args : List Val) : Option (List TrapReason) :=
  (emb.instantiateRun o fuel c (importArgs ims) (hostConfig ims σ0)).bind fun (r, _, es) =>
    (es.lookup name).bind fun f =>
      (emb.callTop o fuel ⟨0⟩ f args r.config).map fun r' =>
        r'.labels.filterMap fun
          | .trap t => some t
          | _ => none

end Session

/-! ## The hosts -/

section Hosts

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

/-- The engine of the fixtures: Core 3.0 at the profile that never fails `memory.grow`. -/
abbrev E0 : CoreEngine := core3 Silmaril.Wasm.SingleThreaded.neverFail

/-- The deterministic first-alternative oracle. -/
abbrev first : Oracle E0 := Oracle.first

/-- **A counting host**: every host function, called with no arguments in host state `n`,
resolves with no results and moves to state `n + 1`; the host state counts the host
callouts. -/
def countG : Nat → HostFuncId → List Val → Option (List Val × Nat)
  | n, _, [] => some ([], n + 1)
  | _, _, _ => none

/-- The embedder over `E0` whose host answers by `countG`. -/
def embCount : Embedder E0 Nat :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := fun _ _ => false,
    host := answerImplS countG }

/-- **A host that never answers**: every host function takes its arguments (`on_start`) and
returns without resolving the call; no host waitable is ever ready. -/
def silentImpl : HostImpl E0 Nat :=
  HostImpl.ofFns fun _ c => do
    let _ ← callVals (.onStart c)
    pure (.cancel .none)

/-- The embedder over `E0` whose host never answers. -/
def embSilent : Embedder E0 Nat :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := fun _ _ => false,
    host := silentImpl }

end Hosts

end Silmaril.Wasm.Component.Reference.LinkedSession
