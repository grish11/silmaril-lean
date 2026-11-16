module

public import Silmaril.Wasm.Game.Accept.Bounds.Thms
public import Silmaril.Wasm.Game.Accept.Strict.Thms
public import Silmaril.Wasm.Game.Accept.Examples
public import Silmaril.Wasm.Game.IOAccept.Examples
public import Silmaril.Wasm.Examples.JsonAccept.Exact.Thms
public import Silmaril.Wasm.Examples.JsonAccept.Automaton.Thms
public import Silmaril.Wasm.Examples.JsonAccept.Stream.Thms
public import Silmaril.Wasm.Examples.EmptyCheck.Defs
public import Silmaril.Wasm.Examples.MemberCheck.Defs
public import Silmaril.Wasm.Abstract.AcceptExport.Thms
public import Silmaril.Wasi.Component.Accept.Examples
public import Silmaril.Wasi.Component.Accept.Strict.Examples
public import Silmaril.Wasi.Component.Accept.Bounds.Thms
public import Silmaril.Wasi.Component.Accept.Repr.Thms
public import Silmaril.Wasi.Component.Accept.Session.Thms
public import Silmaril.Wasi.IOAccept.Examples
public import Silmaril.Wasm.Component.Reference.WIT.Repr.Json.Thms

/-! # Acceptor interpretations of modules and components: a typed catalog

One record per **interpretation shape** of the acceptance development: how a module or a
component is read as an acceptor of a language. Each record names, as checked Lean names (the
double-backtick syntax fails to elaborate on a missing declaration):

* `reading`: the definition of the reading (`bytesLang`, `exportAccepted`, …);
* `theorems`: the theorems that carry the evidence;
* `subject`: what it is about:
  * `.module slug decl`: a **concrete core module**, a Lean `Module` value. Its bytes are encoded
    by `Binaryen.Exe.encodeModule?` (`encodeModule?_sound`: they satisfy the specification's
    binary grammar `Binary.Core.Encodes` for that module). `slug` is its id in the explorer's
    Wasm pages (`tools/wasm-pages`, `leanExamples`). The theorems are about the module value,
    not about the bytes;
  * `.specComponent decl`: a **specification component**, a strategy defined in Lean. No
    compiled component exists for it, and there are no bytes;
  * `.leanFunction decl`: a Lean function (not Wasm) proved equal to a Wasm reading;
  * `.anyModule`, `.anyComponent`: a definition for every module or component, with no concrete
    instance beyond the tests named.
* `basis`: what the evidence rests on: concrete execution semantics, a specification strategy, a
  hypothesis (named), or definitions only;
* `strength`: exact (an equality with a stated language), sound, membership witnesses only, or a
  definition with general laws.

`unsupported` lists the forms that have no interpretation yet, with the reason. `Examples` checks
that the records are well formed (unique ids, every shape covered once by a record or by the
unsupported list).

This is metadata, independent of any serialization. The registry that publishes it to the
explorer is owned by the project registry; this module is the source of the declarations.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Catalog

open Lean (Name)

/-- The interpretation shapes. -/
inductive Shape where
  /-- Module import `accept(ptr: i32, len: i32)`, the bytes of memory `0`. -/
  | importBytes32
  /-- Module import `accept(ptr: i64, len: i64)`. -/
  | importBytes64
  /-- Module import `accept(x: i32)` / `accept(x: i64)`, scalar values. -/
  | importScalar
  /-- Module import, any call (a decoder accepting every call). -/
  | importCall
  /-- Module export `accept(ptr, len) -> i32` after spec instantiation. -/
  | exportPtrLen
  /-- Module: accepted through one import and never through a reject import. -/
  | moduleCombined
  /-- Module: one acceptor set per import (indexed callouts). -/
  | moduleIndexed
  /-- Module: traced I/O relations scoped to export invocations. -/
  | moduleTracedIO
  /-- Module export embedding through the abstract function semantics `wasmFun`. -/
  | moduleAbstract
  /-- The automaton of a module, as an incremental stream acceptor. -/
  | moduleStream
  /-- Component import `accept(list<u8>)`. -/
  | componentImport
  /-- Component export `accept(list<u8>) -> bool`. -/
  | componentExport
  /-- Component: accept and reject functions, combined. -/
  | componentCombined
  /-- Component: indexed acceptor sets (per import, per layout). -/
  | componentIndexed
  /-- Component: relational I/O over legal plays. -/
  | componentIO
  /-- Component: incremental `process`/`query`/`reset` client sessions. -/
  | componentSession
  /-- Component: a WIT type with a representation of Lean values (event streams, JSONL items). -/
  | componentRepr
  /-- Component bounds under canonical-ABI assumptions. -/
  | componentBounds
  /-- Component: multi-call streaming completeness over unbounded inputs. -/
  | componentStreamingComplete
  /-- A compiled component binary interpreted as an acceptor. -/
  | compiledComponent
  /-- A module import `accept(ptr, len)` with a concrete module proved to accept a stated
  language. -/
  | importBytesConcrete
  deriving DecidableEq, Repr

/-- All shapes, for coverage checks. -/
def Shape.all : List Shape :=
  [.importBytes32, .importBytes64, .importScalar, .importCall, .exportPtrLen, .moduleCombined,
    .moduleIndexed, .moduleTracedIO, .moduleAbstract, .moduleStream, .componentImport,
    .componentExport, .componentCombined, .componentIndexed, .componentIO, .componentSession,
    .componentRepr, .componentBounds, .componentStreamingComplete, .compiledComponent,
    .importBytesConcrete]

/-- What an interpretation is about. -/
inductive Subject where
  /-- A concrete core module (a Lean `Module` value), its explorer slug and declaration. -/
  | module (slug : String) (decl : Name)
  /-- A specification component (a strategy), with no compiled binary. -/
  | specComponent (decl : Name)
  /-- A Lean function, not Wasm. -/
  | leanFunction (decl : Name)
  /-- Every module. -/
  | anyModule
  /-- Every component (strategy). -/
  | anyComponent
  deriving Repr

/-- What the evidence rests on. -/
inductive Basis where
  /-- The execution semantics of the subject (Core 3.0 steps, spec instantiation). -/
  | execution
  /-- A specification strategy (component), not a compiled implementation. -/
  | specStrategy
  /-- A named hypothesis, not discharged for any concrete subject. -/
  | hypothesis (name : Name)
  /-- Definitions and their general laws only. -/
  | definitions
  deriving Repr

/-- How strong the evidence is. -/
inductive Strength where
  /-- An equality with a stated language. -/
  | exact
  /-- An inclusion in a stated language. -/
  | sound
  /-- Membership witnesses only. -/
  | witness
  /-- General laws (equivalence invariance, bounds, transport) for every subject. -/
  | laws
  deriving DecidableEq, Repr

/-- **One interpretation.** -/
structure Interpretation where
  /-- A stable identifier. -/
  id : String
  shape : Shape
  subject : Subject
  /-- The language the reading equals or is included in, when one is stated. -/
  language : Option Name := none
  /-- The definition of the reading. -/
  reading : Name
  theorems : List Name
  basis : Basis
  strength : Strength
  /-- Scope and limits, one sentence. -/
  note : String
  deriving Repr

/-- **A form with no interpretation yet.** -/
structure Unsupported where
  shape : Shape
  reason : String
  deriving Repr

/-- The explorer slug of the JSON-subset acceptor (`tools/wasm-pages`). -/
def jsonAcceptSlug : String := "silmaril.wasm.examples.json_accept.prog"

/-- The explorer slug of `exStart` (`tools/wasm-pages`). -/
def exStartSlug : String := "silmaril.wasm.game.examples.ex_start"

/-- The explorer slug of the empty checker `Examples.EmptyCheck.prog`. -/
def emptyCheckSlug : String := "silmaril.wasm.examples.empty_check.prog"

/-- The explorer slug of the membership checker `Examples.MemberCheck.prog`. -/
def memberCheckSlug : String := "silmaril.wasm.examples.member_check.prog"

/-- **The concrete modules of the catalog**, with their explorer slugs: `tools/wasm-pages` encodes
and publishes exactly these (and its other examples). -/
def concreteModules : List (String × String × Name × Silmaril.Wasm.Module) := [
  (jsonAcceptSlug, "Examples.JsonAccept.prog (verified acceptor: JSON integer texts)",
    ``Silmaril.Wasm.Examples.JsonAccept.prog, Silmaril.Wasm.Examples.JsonAccept.prog),
  (exStartSlug, "Game.Examples.exStart (start function calls its import)",
    ``Silmaril.Wasm.Game.Examples.exStart, Silmaril.Wasm.Game.Examples.exStart),
  (emptyCheckSlug, "Examples.EmptyCheck.prog (verified checker: check(ptr, len) answers 0)",
    ``Silmaril.Wasm.Examples.EmptyCheck.prog, Silmaril.Wasm.Examples.EmptyCheck.prog),
  (memberCheckSlug, "Examples.MemberCheck.prog (verified checker: first byte occurs in the rest)",
    ``Silmaril.Wasm.Examples.MemberCheck.prog, Silmaril.Wasm.Examples.MemberCheck.prog)]

/-- The explorer slug of a subject, when it is a concrete module. -/
def Subject.slug? : Subject → Option String
  | .module s _ => some s
  | _ => none

/-- **The interpretations.** -/
def entries : List Interpretation := [
  { id := "module.import.bytes32", shape := .importBytes32, subject := .anyModule,
    reading := ``Silmaril.Wasm.Game.Accept.bytesLang,
    theorems := [``Silmaril.Wasm.Game.Accept.Callout.bytes32_eq_some_iff,
      ``Silmaril.Wasm.Game.Accept.Callout.getElem?_of_segment,
      ``Silmaril.Wasm.Game.Accept.bytesLang_length_lt,
      ``Silmaril.Wasm.Game.Accept.bytesLang_finite,
      ``Silmaril.Wasm.Game.Accept.bytesLang_eq_of_calloutEquiv],
    basis := .execution, strength := .laws,
    note := "The bytes [ptr, ptr+len) of memory 0 at a reachable call of env.accept; lengths < 2^32, finite; decoders tested by kernel evaluation." },
  { id := "module.import.bytes64", shape := .importBytes64, subject := .anyModule,
    reading := ``Silmaril.Wasm.Game.Accept.bytes64Lang,
    theorems := [``Silmaril.Wasm.Game.Accept.Callout.bytes64_eq_some_iff,
      ``Silmaril.Wasm.Game.Accept.bytes64Lang_length_lt,
      ``Silmaril.Wasm.Game.Accept.bytes64Lang_finite],
    basis := .execution, strength := .laws,
    note := "As bytes32 with i64 pointer and length (memory64); lengths < 2^64." },
  { id := "module.import.scalar", shape := .importScalar, subject := .anyModule,
    reading := ``Silmaril.Wasm.Game.Accept.i32Lang,
    theorems := [``Silmaril.Wasm.Game.Accept.Callout.i32?_eq_some_iff,
      ``Silmaril.Wasm.Game.Accept.Callout.i64?_eq_some_iff, ``Silmaril.Wasm.Game.Accept.i64Lang],
    basis := .execution, strength := .laws,
    note := "accept(x: i32) and accept(x: i64): the argument values of reachable calls." },
  { id := "module.import.call.exStart", shape := .importCall,
    subject := .module exStartSlug ``Silmaril.Wasm.Game.Examples.exStart,
    reading := ``Silmaril.Wasm.Game.Accept.accepted,
    theorems := [``Silmaril.Wasm.Game.Accept.Examples.exStart_callout,
      ``Silmaril.Wasm.Game.Accept.Examples.exStart_accepts],
    basis := .execution, strength := .witness,
    note := "exStart's start function calls env.f during spec instantiation, for every profile; non-vacuity of the callout reading, not a byte language." },
  { id := "module.export.json_accept", shape := .exportPtrLen,
    subject := .module jsonAcceptSlug ``Silmaril.Wasm.Examples.JsonAccept.prog,
    language := some ``Silmaril.Wasm.Examples.JsonAccept.intText,
    reading := ``Silmaril.Wasm.Game.Accept.exportAccepted,
    theorems := [``Silmaril.Wasm.Examples.JsonAccept.accept_total,
      ``Silmaril.Wasm.Examples.JsonAccept.exportAccepted_eq,
      ``Silmaril.Wasm.Examples.JsonAccept.exportRejected_eq,
      ``Silmaril.Wasm.Examples.JsonAccept.exportAccepted_eq_dfa,
      ``Silmaril.Wasm.Examples.JsonAccept.exportAccepted_subset_json],
    basis := .execution, strength := .exact,
    note := "Exactly the JSON texts that are one integer (with whitespace) shorter than 2^32 bytes, for every profile and any non-empty host set; a subset of JSON, not all of JSON; total (variant len - i)." },
  { id := "module.combined.json_accept", shape := .moduleCombined,
    subject := .module jsonAcceptSlug ``Silmaril.Wasm.Examples.JsonAccept.prog,
    language := some ``Silmaril.Wasm.Examples.JsonAccept.intText,
    reading := ``Silmaril.Wasm.Game.Accept.exportAcceptedNotRejected,
    theorems := [``Silmaril.Wasm.Game.Accept.exportAcceptedNotRejected_eq_acceptsSafely,
      ``Silmaril.Wasm.Examples.JsonAccept.exportAcceptedNotRejected_eq,
      ``Silmaril.Wasm.Examples.JsonAccept.acceptsSafely_eq,
      ``Silmaril.Wasm.Examples.JsonAccept.exportAccepted_disjoint_rejected],
    basis := .execution, strength := .exact,
    note := "Some run returns 1 and no run returns 0, over the same runs and hosts." },
  { id := "module.combined.callouts", shape := .moduleCombined, subject := .anyModule,
    reading := ``Silmaril.Wasm.Game.Accept.acceptedNotRejected,
    theorems := [``Silmaril.Wasm.Game.Accept.acceptedNotRejected_eq_acceptsSafely,
      ``Silmaril.Wasm.Game.Accept.acceptedNotRejected_self,
      ``Silmaril.Wasm.Game.Accept.ModuleAcceptor.strictLang_self,
      ``Silmaril.Wasm.Game.Accept.not_mem_acceptedNotRejected_of_no_callout,
      ``Silmaril.Wasm.Game.Accept.neverRejected_eq_of_calloutEquiv],
    basis := .execution, strength := .laws,
    note := "Called through accept in some run and through reject in none; no call: not accepted; one import for both: empty." },
  { id := "module.indexed", shape := .moduleIndexed, subject := .anyModule,
    reading := ``Silmaril.Wasm.Game.Accept.indexed,
    theorems := [``Silmaril.Wasm.Game.Accept.accepted_eq_iUnion_indexed,
      ``Silmaril.Wasm.Game.Accept.indexed_eq_of_calls_eq],
    basis := .execution, strength := .laws,
    note := "One acceptor set per import index." },
  { id := "module.traced_io.exStart", shape := .moduleTracedIO,
    subject := .module exStartSlug ``Silmaril.Wasm.Game.Examples.exStart,
    reading := ``Silmaril.Wasm.Game.IOAccept.entryIORuns,
    theorems := [``Silmaril.Wasm.Game.IOAccept.Examples.run_tsession,
      ``Silmaril.Wasm.Game.IOAccept.Examples.run_triggers,
      ``Silmaril.Wasm.Game.IOAccept.callouts_eq_traced],
    basis := .execution, strength := .witness,
    note := "exStart's export run triggers its call of env.f; the start function's own call is outside every scope; no reentrancy." },
  { id := "module.abstract.json_accept", shape := .moduleAbstract,
    subject := .module jsonAcceptSlug ``Silmaril.Wasm.Examples.JsonAccept.prog,
    language := some ``Silmaril.Wasm.Examples.JsonAccept.intText,
    reading := ``Silmaril.Wasm.Abstract.Accept.absExportRun,
    theorems := [``Silmaril.Wasm.Abstract.Accept.exportAcceptedNotRejected_eq_abs,
      ``Silmaril.Wasm.Abstract.Accept.exportRun_eq,
      ``Silmaril.Wasm.Examples.JsonAccept.absAcceptsSafely_eq],
    basis := .execution, strength := .exact,
    note := "The export embedding read through the abstract function semantics wasmFun: equal verdicts." },
  { id := "module.stream.json_accept", shape := .moduleStream,
    subject := .leanFunction ``Silmaril.Wasm.Examples.JsonAccept.streamAcceptor,
    language := some ``Silmaril.Wasm.Examples.JsonAccept.intText,
    reading := ``Silmaril.Wasm.Examples.JsonAccept.streamAcceptor,
    theorems := [``Silmaril.Wasm.Examples.JsonAccept.streamAcceptor_correctInterleaved,
      ``Silmaril.Wasm.Examples.JsonAccept.answer_eq_wasm,
      ``Silmaril.Wasm.Examples.JsonAccept.boundaryAnswer_eq_wasm],
    basis := .execution, strength := .exact,
    note := "The module's automaton in Lean, fed chunk by chunk; equal to the module's verdict below 2^32 bytes. Not a second Wasm module." },
  { id := "component.import.spec", shape := .componentImport,
    subject := .specComponent ``Silmaril.Wasi.Accept.importAcceptor,
    reading := ``Silmaril.Wasi.Accept.bytesLang,
    theorems := [``Silmaril.Wasi.Accept.Examples.bytesLang_importAcceptor,
      ``Silmaril.Wasi.Accept.Examples.importAcceptor_exact],
    basis := .specStrategy, strength := .exact,
    note := "A specification component calling accept(list<u8>) with exactly the words of L; no compiled component." },
  { id := "component.export.spec", shape := .componentExport,
    subject := .specComponent ``Silmaril.Wasi.Accept.exportAcceptor,
    reading := ``Silmaril.Wasi.Accept.exportBytesLang,
    theorems := [``Silmaril.Wasi.Accept.Examples.exportBytesLang_exportAcceptor],
    basis := .specStrategy, strength := .exact,
    note := "A specification component whose export accept(list<u8>) -> bool returns true exactly on L; no compiled component." },
  { id := "component.combined.spec", shape := .componentCombined,
    subject := .specComponent ``Silmaril.Wasi.Accept.verdictComponent,
    reading := ``Silmaril.Wasi.Accept.exportAcceptedNotRejected,
    theorems := [``Silmaril.Wasi.Accept.exportAcceptedNotRejected_eq_acceptsSafely,
      ``Silmaril.Wasi.Accept.importAcceptedNotRejected_eq_acceptsSafely,
      ``Silmaril.Wasi.Accept.Examples.strict_verdictComponent,
      ``Silmaril.Wasi.Accept.importAcceptedNotRejected_self,
      ``Silmaril.Wasi.Accept.retWith_conflicts],
    basis := .specStrategy, strength := .exact,
    note := "accept(w) may return true on A, reject(w) false on R: combined language A \\ R; an export returning true and false never conflicts." },
  { id := "component.indexed", shape := .componentIndexed, subject := .anyComponent,
    reading := ``Silmaril.Wasi.Accept.importIndexed,
    theorems := [``Silmaril.Wasi.Accept.eraseSome_importIndexed,
      ``Silmaril.Wasi.Accept.layoutIndexed_of_getElem?],
    basis := .definitions, strength := .laws,
    note := "One acceptor set per import, and per argument position of a layout." },
  { id := "component.io", shape := .componentIO, subject := .anyComponent,
    reading := ``Silmaril.Wasi.IOAccept.entryIORuns,
    theorems := [``Silmaril.Wasi.IOAccept.entryIORuns_eq_of_traces,
      ``Silmaril.Wasi.IOAccept.shallow_of_legal, ``Silmaril.Wasi.IOAccept.ret_after_call],
    basis := .definitions, strength := .laws,
    note := "Relational I/O scoped to export calls of legal plays; invariance only, no abstract-model statement." },
  { id := "component.session", shape := .componentSession, subject := .anyComponent,
    reading := ``Silmaril.Wasi.Accept.sessionTraces,
    theorems := [``Silmaril.Wasi.Accept.freshFeedsQuery_sound,
      ``Silmaril.Wasi.Accept.feedsQuery_sound, ``Silmaril.Wasi.exportAlt_of_legal],
    basis := .hypothesis ``Silmaril.Wasi.Accept.StreamCorrect, strength := .sound,
    note := "Given StreamCorrect (and QueryTotal after resets): each query answer is membership of the chunks fed; no concrete component discharges StreamCorrect." },
  { id := "component.repr.json_events", shape := .componentRepr, subject := .anyComponent,
    reading := ``Silmaril.Wasi.Accept.reprLang,
    theorems := [``Silmaril.Wasi.Accept.sound_reprLang_iff,
      ``Silmaril.Wasi.Accept.completeWithin_reprLang_iff,
      ``Silmaril.Wasm.Component.WIT.Json.treeEquiv,
      ``Silmaril.Wasm.Component.WIT.Json.mem_eventLangAt_iff,
      ``Silmaril.Wasm.Component.WIT.Json.linesEquiv],
    basis := .definitions, strength := .laws,
    note := "Lean values whose WIT representation is accepted (JSON event streams as list<json-event>, JSONL items as list<list<u8>>); no byte-to-event lexer." },
  { id := "component.bounds.canon", shape := .componentBounds, subject := .anyComponent,
    reading := ``Silmaril.Wasi.Accept.bytesLang,
    theorems := [``Silmaril.Wasi.Accept.bytesLang_length_lt_of_canonLowerAccept,
      ``Silmaril.Wasi.Accept.bytesLang_finite_of_canonLowerAccept],
    basis := .hypothesis ``Silmaril.Wasi.Accept.CanonLowerAcceptBy, strength := .laws,
    note := "Length bounds and finiteness only under a canonical-ABI lowering hypothesis that no adapter is proved to satisfy." }]

/-- **The forms with no interpretation yet.** -/
def unsupported : List Unsupported := [
  { shape := .compiledComponent,
    reason := "No compiled component binary is interpreted as an acceptor: the component readings are proved for strategies, and no compiled component is related to one." },
  { shape := .componentStreamingComplete,
    reason := "Completeness of a multi-call streaming component over unbounded inputs is not stated; only the one-call module bound is (Wasm.Game.Accept.Complete)." },
  { shape := .importBytesConcrete,
    reason := "No concrete module is proved to accept a stated byte language through an import accept(ptr, len); the import reading is tested on decoders and on exStart's unit call only." }]

end Silmaril.Wasi.Accept.Catalog
