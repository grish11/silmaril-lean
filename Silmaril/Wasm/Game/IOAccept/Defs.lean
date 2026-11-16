module

public import Silmaril.Wasm.Game.Accept.Defs
public import Silmaril.Semantics.Accept.IO.Defs

/-! # Traced I/O acceptance of core Wasm modules

`Silmaril.Wasm.Game.Accept.Session` is a reachability predicate: it records no trace, so the
order of a module's callouts, the export invocation they belong to and the host answers that
fed them are lost, and `Callouts` is a set. This file refines it by **traced sessions**
(`TSession`): the same runs, recording role tags (`Silmaril.Accept.IO.Tag`) on the way, so
that the scoped relations of `Silmaril.Accept.IO` (`triggers`, `episodes`, `retTriggers`,
`returns`) apply to modules.

## Roles

A `Roles X I O C` structure holds the decoders, each defaulting to "not observed":

* `entry a args : Option X`: the argument observed when the environment invokes the export at
  function address `a` with the raw arguments `args`;
* `result vs mem : Option C`: the result observed when an invocation returns the values `vs`
  with the instance's memory holding `mem` (a trap or an uncaught exception is `none`);
* `callIn o : Option I`, `callOut o : Option O`: the input and output observed at a callout
  `o : Callout` (an imported `input(i)` or `output(o)`), read when the call is made;
* `answerIn o w : Option I`: the input observed when the host answers the callout `o` with
  `w : HostReply`, its raw `Result` and the bytes of the instance's memory **after** the
  answer (an imported `read() -> i`, or a `read(buf, len)` that fills the memory).

Host answers are decodable: `UStep.answer` exposes the reply `a : UReply` (the new store and
the raw result) of the environment's `L.Ans`, and the traced session reads `answerIn` off it.

## Traced sessions

`TSession P L m memAddr R c₀ q₀ addrs p w x ts`: from the instantiation configuration `c₀`, in
phase `p` (`Phase`: instantiating, inside an invocation, or idle between invocations), the
product state `x` is reached with the tags `ts` (oldest first); `w` records that the callout
at the current redex has been tagged. The constructors are those of `Session`:

* `start`; `internal`: a host-free Core step (no tag);
* `call`: at a host-call redex (`decompose?`), the callout's `callIn`/`callOut` tags, in that
  order (`Tag.inp` before `Tag.out`, so a call that is both reads before it writes); the redex
  is tagged once (`w`);
* `answer`: the host answer step of `UStep` with its `answerIn` tag;
* `invoke`: an export invocation after a finished run, tagged `Tag.enter (entry a args)`;
* `ret`: a finished invocation, tagged `Tag.exit`: `result vs mem` for returned values, `none`
  for a trap or an uncaught exception. It moves to `idle`, where the next `invoke` may happen.

A host divergence (`UStep.silent`) is a self-loop of the product state and records nothing.
Callouts of a redex whose host code is not an import index (a host function added by the
environment and called through a reference) are not `CalloutOf` and are not tagged.

`tagTraces P Envs memIdx m R` are the tag lists of all traced sessions, over instantiations and
environments of the class `Envs`, as in `Callouts`. `ioRuns` and `entryIORuns` are
`inputRunsOf` and `entryRunsOf` of their scoped forms `bracket '' tagTraces …`; the four
relations of `Silmaril.Accept.IO` come for free: `triggers (ioRuns …)`, `episodes (ioRuns …)`,
`retTriggers (ioRuns …)`, `returns (entryIORuns …)`, and so on.

## Scope of the model

* **Internal outputs outside any invocation.** Callouts of the instantiation phase (segment
  initialisation and the start function) are tagged before any `enter`; `bracket` assigns them
  no scope and drops them (`Silmaril.Wasm.Game.IOAccept.TSession.bracket_eq`). They are still
  `Callouts` of the module.
* **No reentrancy.** The environment invokes exports only after a finished run, and a host
  answer is a single relation step: a host call cannot call back into the module. Every traced
  session is therefore flat (`TSession.openScan`): `enter` and `exit` alternate, and each
  scope is one export invocation.
* **Divergence and cut-off runs.** Traces are finite prefixes; an invocation that does not
  finish has no `exit` and its runs have result `none`.

New definitions (no source); the semantics are those of `Silmaril.Wasm.Game.Accept` and
`Silmaril.Wasm.Game.Untyped`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.IOAccept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept Silmaril.Accept.IO

/-! ## Observations -/

/-- The bytes of the memory at store address `memAddr`, if any. -/
def memOf (memAddr : Option Nat) (s : Store Nat) : Option ByteArray :=
  (memAddr.bind fun a => s.mems[a]?).map MemInst.bytes

/-- The callout at the configuration `c` of an instance of `m` (`CalloutOf` as a function). -/
def calloutAt? (m : Module) (memAddr : Option Nat) (c : Config Nat) : Option Callout :=
  (decompose? c.store c.code).bind fun (_, _, h, args) =>
    (m.imports[h]?).map fun i => ⟨(i.moduleName, i.name), args, memOf memAddr c.store⟩

/-- A host answer, observed: the raw result and the bytes of the memory after the answer. -/
structure HostReply where
  /-- The raw result returned by the host. -/
  result : Result
  /-- The bytes of the instance's memory in the answer's store (`none` without a memory). -/
  mem : Option ByteArray

/-- The role decoders of a traced session. Each defaults to "not observed". -/
structure Roles (X I O C : Type) where
  /-- The argument observed at the invocation of the export at an address with raw arguments
  (`none`: the invocation still opens a scope, unobserved). -/
  entry : Nat → List Val → Option X := fun _ _ => none
  /-- The result observed when an invocation returns values, with the memory at return. -/
  result : List Val → Option ByteArray → Option C := fun _ _ => none
  /-- The input observed when an import is called. -/
  callIn : Callout → Option I := fun _ => none
  /-- The output observed when an import is called. -/
  callOut : Callout → Option O := fun _ => none
  /-- The input observed when the host answers a call. -/
  answerIn : Callout → HostReply → Option I := fun _ _ => none

namespace Roles

variable {X I O C : Type} (R : Roles X I O C)

/-- The tags of a callout: its input, then its output. -/
def callTags (o : Callout) : List (Tag X I O C) :=
  (R.callIn o).toList.map .inp ++ (R.callOut o).toList.map .out

/-- The tags of a host answer. -/
def answerTags (o : Callout) (w : HostReply) : List (Tag X I O C) :=
  (R.answerIn o w).toList.map .inp

/-- The observed result of a finished invocation: decoded values; a trap or an uncaught
exception is `none`. -/
def exitVal : Result → Option ByteArray → Option C
  | .values vs, mem => R.result vs mem
  | _, _ => none

end Roles

/-- The value `dec o` of a call of the import `imp`, and nothing for other imports: the
output role of `accepted dec … imp`. -/
def outputVia {α : Type} (imp : String × String) (dec : Callout → Option α) (o : Callout) :
    Option α :=
  if o.imp = imp then dec o else none

/-! ## Traced sessions -/

/-- The phase of a traced session. -/
inductive Phase where
  /-- Instantiation is running (segment initialisation, start function). -/
  | inst
  /-- An export invocation is running. -/
  | run
  /-- The last invocation has finished and been tagged. -/
  | idle
  deriving DecidableEq, Repr

/-- The `Session` flag of a phase: instantiation has finished. -/
def Phase.started : Phase → Bool
  | .inst => false
  | _ => true

variable {X I O C : Type}

/-- **Traced sessions** of an instance of `m` (memory at store address `memAddr`), decoded by
`R`: `Session`'s runs, recording role tags. See the module docstring. -/
inductive TSession (P : Profile) (L : SEnv UImp) (m : Module) (memAddr : Option Nat)
    (R : Roles X I O C) (c₀ : Config Nat) (q₀ : L.S) (addrs : List Nat) :
    Phase → Bool → Config Nat × L.S → List (Tag X I O C) → Prop where
  /-- The instantiation configuration. -/
  | start : TSession P L m memAddr R c₀ q₀ addrs .inst false (c₀, q₀) []
  /-- A host-free Core step. -/
  | internal {p : Phase} {w : Bool} {c c' : Config Nat} {q : L.S} {ts : List (Tag X I O C)}
      (h : TSession P L m memAddr R c₀ q₀ addrs p w (c, q) ts)
      (st : Step P (fun _ _ _ _ => False) c c') :
      TSession P L m memAddr R c₀ q₀ addrs p false (c', q) ts
  /-- The code is at a host-call redex: tag the callout once. -/
  | call {p : Phase} {c : Config Nat} {q : L.S} {ts : List (Tag X I O C)} {E : Ctx}
      {fa h : Nat} {args : List Val}
      (hs : TSession P L m memAddr R c₀ q₀ addrs p false (c, q) ts)
      (hd : decompose? c.store c.code = some (E, fa, h, args)) :
      TSession P L m memAddr R c₀ q₀ addrs p true (c, q)
        (ts ++ (calloutAt? m memAddr c).elim [] R.callTags)
  /-- The host answers the tagged call with `a` (`UStep.answer`). -/
  | answer {p : Phase} {c : Config Nat} {q q' : L.S} {ts : List (Tag X I O C)} {E : Ctx}
      {fa h : Nat} {args : List Val} {a : UReply}
      (hs : TSession P L m memAddr R c₀ q₀ addrs p true (c, q) ts)
      (hd : decompose? c.store c.code = some (E, fa, h, args))
      (ans : L.Ans q ⟨h, c.store, args⟩ a q') :
      TSession P L m memAddr R c₀ q₀ addrs p false
        (⟨a.store, c.frame, E.fill a.result.toAdmin⟩, q')
        (ts ++ (calloutAt? m memAddr c).elim [] fun o =>
          R.answerTags o ⟨a.result, memOf memAddr a.store⟩)
  /-- The environment invokes an export after a finished run (instantiation, or a tagged
  invocation). -/
  | invoke {p : Phase} {w : Bool} {c : Config Nat} {q : L.S} {ts : List (Tag X I O C)}
      {a : Nat} {args : List Val}
      (hs : TSession P L m memAddr R c₀ q₀ addrs p w (c, q) ts) (hp : p ≠ .run)
      (fin : Finished p.started c) (ha : a ∈ addrs) (ok : InvokeOk c.store a args) :
      TSession P L m memAddr R c₀ q₀ addrs .run false (invoke c.store a args, q)
        (ts ++ [.enter (R.entry a args)])
  /-- A running invocation has finished with the result `r`. -/
  | ret {w : Bool} {c : Config Nat} {q : L.S} {ts : List (Tag X I O C)} {r : Result}
      (hs : TSession P L m memAddr R c₀ q₀ addrs .run w (c, q) ts) (hr : c.code = r.toAdmin) :
      TSession P L m memAddr R c₀ q₀ addrs .idle false (c, q)
        (ts ++ [.exit (R.exitVal r (memOf memAddr c.store))])

/-! ## Traces, runs and relations of a module -/

/-- **The tag traces of a module**: over every instantiation, every environment of the class
`Envs` and every traced session (memory index `memIdx` of the instance). -/
def tagTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (R : Roles X I O C) : Set (List (Tag X I O C)) :=
  {ts | ∃ (mt : CModuleType) (Is : ScalarInstance) (c₀ : Config Nat),
    IsSpecInstance m mt Is c₀ ∧
    ∃ (L : SEnv UImp) (q₀ : L.S), Envs Is.store L ∧
    ∃ (p : Phase) (w : Bool) (x : Config Nat × L.S),
      TSession P L m c₀.frame.module.mems[memIdx]? R c₀ q₀ Is.addrs p w x ts}

/-- **Input-window runs of a module**: an input (`callIn`, `answerIn`) and the outputs of the
same invocation after it, up to the next input or the invocation's end. -/
def ioRuns (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (R : Roles X I O C) : Set (Run I O C) :=
  inputRunsOf (bracket '' tagTraces P Envs memIdx m R)

/-- **Entry runs of a module**: the observed argument of an export invocation, all outputs of
the invocation and its result. -/
def entryIORuns (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (R : Roles X I O C) : Set (Run X O C) :=
  entryRunsOf (bracket '' tagTraces P Envs memIdx m R)

/-! ## Flatness -/

/-- Scan a tag list from outside (`false`) or inside (`true`) an invocation: the final position,
or `none` when an `enter` occurs inside an invocation or an `exit` outside one. -/
def openScan : Bool → List (Tag X I O C) → Option Bool
  | b, [] => some b
  | false, .enter _ :: ts => openScan true ts
  | true, .enter _ :: _ => none
  | true, .exit _ :: ts => openScan false ts
  | false, .exit _ :: _ => none
  | b, .inp _ :: ts => openScan b ts
  | b, .out _ :: ts => openScan b ts

end Silmaril.Wasm.Game.IOAccept
