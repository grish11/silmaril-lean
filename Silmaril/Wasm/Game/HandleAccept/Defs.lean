module

public import Silmaril.Wasm.Logic.GameLink.Defs
public import Silmaril.Wasm.Verify.Checker.Defs
public import Silmaril.Semantics.Accept.Handle.Defs
public import Silmaril.Formats.SExp.Api.Defs

/-! # Handle-based tree acceptance of core Wasm modules

The handle APIs of `Silmaril.Semantics.Accept.Handle` read off the **plays of the Core 3.0
instance strategy** `I.strategy P s` (`Silmaril.Wasm.Game`): every profile, every environment
(import answers are arbitrary typed Opponent moves), every sequence of export calls. A play is a
list of moves; an import call is the Proponent move `.inl (.ask e)` with `e = ⟨i, args⟩` (import
index and typed arguments), its answer the Opponent move `.inl (.ans e v)` right after it
(legal plays alternate; host calls are atomic). Both moves carry the import and its arguments,
so events are decoded **per move**:

* `decAsk e : Option Ev`: the event of an import call, observed when it is made (for instance
  `accept(h)`);
* `decAns e v : Option Ev`: the event of an answered call (for instance a read `kind(h) = k`, or
  a write `word(x) = h`);
* `enter : Option Ev`: the event of an **export call** `.inr (.ask _)` (the environment calling
  the module), `some .enter` for the handle APIs (`REv.enter`, `WEv.enter`): the export-call
  boundary at which a call-local trap (`OnInvalid.callTrap`) resumes. Export returns are not
  events.

The instance keeps its store across export calls (`ScalarInstance.strategy`), so a trap aborts
only the current export call: the decoded trace of a play contains every export call, and the
module languages read call boundaries.

`playEvents enter decAsk decAns p` is the decoded event trace of a play, `handleTraces σ …` the
decoded traces of a strategy, and `moduleReaderLang` / `moduleWriterLang` the reader and writer
languages (`Silmaril.Accept.Handle.readerLang`, `writerLang`) of a module's instance
(`Silmaril.Wasm.Verify.instOf`) over every profile `P` given as a parameter.

**Scope.** Game moves carry argument values and results but not memory contents, so this reading
covers memory-free imports: `i32`/`i64` arguments and results (`word(i64)`, `nil()`, `cons`,
fixed-arity `tag(args…, c₁, …, cₙ)`, the readers `kind`, `car`, `cdr`, `count`, `child`, `word`).
Imports passing strings or lists through linear memory (`symbol(string)`,
`sexp(list<i32>)`) need the memory-observing sessions of `Silmaril.Wasm.Game.Accept`
(`Callout.mem`); their decoders are not defined here.

## The cons reader API (`ConsImports`)

Imports by index: `kind : [i32] → [i32]` (`0` nil, `1` atom, `2` cons; any other code is an
ill-typed answer, never correct), `car`, `cdr : [i32] → [i32]`, `word : [i32] → [i64]` (the atom
of a handle, as an `i64` word) and `accept : [i32] → []`. `consDecAsk`/`consDecAns` decode them
into `REv (ConsQ i32) (ConsA i64 i32) i32`.

## Assume/guarantee specifications from a fixed environment

For a fixed environment `ρ` and a language `L`, `readerISpec` is the import specification whose
answers are the **correct answers in `ρ`** (`Ii.post`, per move) and whose `accept` calls must
name a handle denoting a member of `L` (`Ii.pre`). `Silmaril.Wasm.Logic.GameLink.GameSat` for
it is a Hoare-logic obligation on the module's code, and gives (`Thms`) that the module's reader
language under the trapping read policy is included in `L`, for every accept policy but `ub`
(in particular the Wasm-facing call-local trap).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec)

universe u

/-! ## Decoding plays -/

variable {E F : Sig.{0}} {Ev : Type}

/-- The decoded events of a play: export calls as `enter`, import calls through `decAsk`, their
answers through `decAns`; export returns are not events. -/
def playEvents (enter : Option Ev) (decAsk : E.Op → Option Ev)
    (decAns : (e : E.Op) → E.Ar e → Option Ev) : List (Move E F) → List Ev
  | [] => []
  | .inl (.ask e) :: p => (decAsk e).toList ++ playEvents enter decAsk decAns p
  | .inl (.ans e v) :: p => (decAns e v).toList ++ playEvents enter decAsk decAns p
  | .inr (.ask _) :: p => enter.toList ++ playEvents enter decAsk decAns p
  | .inr (.ans _ _) :: p => playEvents enter decAsk decAns p

/-- The decoded traces of a strategy, with export calls decoded as `enter`. -/
def handleTraces (σ : Strategy E F) (enter : Option Ev) (decAsk : E.Op → Option Ev)
    (decAns : (e : E.Op) → E.Ar e → Option Ev) : Set (List Ev) :=
  {t | ∃ p ∈ σ, t = playEvents enter decAsk decAns p}

/-! ## Values -/

/-- A single `i32` argument. -/
def i32Arg : List Val → Option (BitVec 32)
  | [.num ⟨.int .i32, h⟩] => some h
  | _ => none

/-- A single `i32` result. -/
def i32Res : List Val → Option (BitVec 32)
  | [.num ⟨.int .i32, h⟩] => some h
  | _ => none

/-- A single `i64` result. -/
def i64Res : List Val → Option (BitVec 64)
  | [.num ⟨.int .i64, w⟩] => some w
  | _ => none

/-! ## The cons reader API -/

/-- Import indices of the cons reader API. -/
structure ConsImports where
  kind : Nat
  car : Nat
  cdr : Nat
  word : Nat
  accept : Nat

/-- The cons reader events over `i32` handles and `i64` words. -/
abbrev ConsEv := REv (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32)) (BitVec 32)

/-- The answer of `kind`: `0` nil, `1` atom, `2` cons; other codes are ill-typed answers. -/
def kindAns (k : BitVec 32) : ConsA (BitVec 64) (BitVec 32) :=
  if k = 0 then .kind .nil else if k = 1 then .kind .atom else if k = 2 then .kind .cons
  else .handle k

/-- The returned values of an answer (`none` for a trap or an exception). -/
def ansVals {ft : FnType} : Answer ft → Option (List Val)
  | .values vs => some vs.1
  | _ => none

variable {ts : List FnType}

/-- Calls of `accept(h)`. -/
def consDecAsk (ix : ConsImports) (e : (ifaceSig ts).Op) : Option ConsEv :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept else none

/-- Answers of `kind`, `car`, `cdr` and `word`. -/
def consDecAns (ix : ConsImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option ConsEv := do
  let h ← i32Arg e.2.1
  let vs ← ansVals v
  if e.1.val = ix.kind then return .read (.kind h) (kindAns (← i32Res vs))
  else if e.1.val = ix.car then return .read (.car h) (.handle (← i32Res vs))
  else if e.1.val = ix.cdr then return .read (.cdr h) (.handle (← i32Res vs))
  else if e.1.val = ix.word then return .read (.atom h) (.atom (← i64Res vs))
  else none

/-! ## Languages of modules -/

/-- **The reader language of a module** through the cons reader API: the trees its instance
accepts in some environment of `Envs`, for the profile `P`. -/
noncomputable def moduleConsLang (P : Profile) (m : Module) (ix : ConsImports)
    (pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) : Set (SExp2 (BitVec 64)) :=
  readerLang (consR (BitVec 64) (BitVec 32)) pol oa Envs
    (handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some .enter)
      (consDecAsk ix) (consDecAns ix))

/-- **The assume/guarantee specification of a reader checker** in the fixed environment `ρ`:
answers are correct in `ρ`; `accept` names a member of `L`. -/
def consISpec (ix : ConsImports) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (L : Set (SExp2 (BitVec 64))) : ISpec (ifaceSig ts) where
  pre e := ∀ h, consDecAsk ix e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  post e v := ∀ q a, consDecAns ix e v = some (.read q a) →
    (consR (BitVec 64) (BitVec 32)).valid ρ q ∧ (consR (BitVec 64) (BitVec 32)).ok ρ q a

/-- The export specification allowing everything. -/
def topISpec (F : Sig.{0}) : ISpec F := ⟨fun _ => True, fun _ _ => True⟩

end Silmaril.Wasm.Game.HandleAccept
