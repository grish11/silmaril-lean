module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Loader.Operational.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence.Recursive.Call (Arguments ClosureAt)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping Operands RunsAt Spread expressionAt)
open Functions
open Lists (State Outcome)
open Loader (Manifest Session)

local notation "Expr" => Lowering.Resolve.SourceExpr

@[expose] def block (alias : String) (globals : List String) : LexicalBlock :=
  ⟨[alias], [], globals⟩

/-- Loads bind file-local names. Ordinary module assignments write globals. -/
@[expose] def readSlot (alias name : String) : Binding :=
  if name = alias then fileSlot name else globalSlot name

structure Invocation (alias : String) (globals : List String) where
  callee : String
  declared : callee = alias ∨ callee ∈ globals
  legal : callee.toList.head? ≠ some '$'
  destination : String
  destinationGlobal : destination ∈ globals
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments (block alias globals) arguments codes reads
  keywords : Operands (block alias globals)
  star : Option (Spread (block alias globals)) := none
  mapping : Option (Mapping (block alias globals)) := none

@[expose] def Invocation.source {alias globals} (call : Invocation alias globals) : Expr :=
  .call (.scalar (.read call.callee)) call.arguments call.keywords.source
    (call.star.map Spread.source) (call.mapping.map Mapping.source)

@[expose] def Invocation.code {alias globals} (call : Invocation alias globals) : Lowering.Expr :=
  expressionAt (readSlot alias call.callee) call.codes call.keywords.codes
    (call.star.map Spread.code) (call.mapping.map Mapping.code)

/-- A checked name copy propagates the original callable. Other assignments
forget the destination's previous provenance. -/
inductive Copy (alias : String) : Expr → Lowering.Expr → Type where
  | forget {source code} : Copy alias source code
  | name (name : String) : Copy alias (.scalar (.read name)) (Leaf.readOperand (readSlot alias name))

@[expose] def Copy.track {alias source code} (copy : Copy alias source code) (env : Environment) : Option Callable :=
  match copy with
  | .forget => none
  | .name read => env read

inductive Step (alias : String) (globals : List String) where
  | assign (destination : String) (declared : destination ∈ globals) {source : Expr}
      {code : Lowering.Expr} {reads : List Binding} :
      Body.Operand (block alias globals) source code reads → Copy alias source code → Step alias globals
  | invoke (call : Invocation alias globals)

@[expose] def Step.destination {alias globals} : Step alias globals → String
  | .assign name .. => name
  | .invoke call => call.destination

@[expose] def Step.source {alias globals} : Step alias globals → Command
  | .assign name _ (source := source) _ _ => .assign name source
  | .invoke call => .assign call.destination call.source

@[expose] def Step.code {alias globals} : Step alias globals → Modules.Command
  | .assign name _ (code := code) _ _ => .exec (.assignExpr name code)
  | .invoke call => .exec (.assignExpr call.destination call.code)

@[expose] def Step.advance {alias globals} (env : Environment) : Step alias globals → Environment
  | .assign destination _ _ copy => update env destination (copy.track env)
  | .invoke call =>
    update env call.destination ((env call.callee).bind fun callee => callee.returned.map Callable.nested)

/-- Source-order provenance enables each call and describes the destination
after its successful return. This judgment contains no heap evidence. -/
@[expose] def ReadyFor {alias : String} {globals : List String} (env : Environment) :
    List (Step alias globals) → Prop
  | [] => True
  | first :: rest =>
    match first with
    | .assign .. => ReadyFor (first.advance env) rest
    | .invoke call => ∃ callee, env call.callee = some callee ∧ ReadyFor (first.advance env) rest

/-- The consumer declares one renamed public import and a finite suite.
The globals are collected from the suite's assignment targets. -/
structure Consumer where
  label : String
  name : String
  alias : String
  publicName : Modules.isPublic name = true
  globals : List String
  body : List (Step alias globals)
  declared : body.map Step.destination = globals
  separate : alias ∉ globals

@[expose] def Consumer.item (plan : Consumer) : Modules.Import :=
  ⟨plan.name, plan.alias⟩

@[expose] def Consumer.commands (plan : Consumer) : List Command :=
  .load plan.label [plan.item] :: plan.body.map Step.source

@[expose] def Consumer.code (plan : Consumer) : List Modules.Command :=
  .load plan.label [plan.item] :: plan.body.map Step.code

@[expose] def initial (alias : String) (callee : Callable) : Environment :=
  update (fun _ => none) alias (some callee)

/-- Producer zero has no dependencies. Consumer one has just the one
requester-relative label. Both use the producer's emitted table. -/
@[expose] def graph (producer consumer : ResolvedModule) (plan : Consumer) : Manifest :=
  #[⟨producer.source, []⟩, ⟨consumer.source, [(plan.label, 0)]⟩]

/-- The source profile tracks either a producer export or a name outside the
producer's declared globals. The consumer supplies no declaration or address. -/
@[expose] def Covered (exports : Environment) (producer : List Command) (plan : Consumer) : Prop :=
  (∃ callee, exports plan.name = some callee ∧ ReadyFor (initial plan.alias callee) plan.body) ∨
    plan.name ∉ Trace.names producer

@[expose] def reachedSession {α : Type} : Loader.Result α → Session
  | .ok _ s | .error _ s => s

/-- Use module publication, with the loader's error attribution and success
cache. This observation is shared by the independent source rules. -/
@[expose] def observed (id : Loader.ModuleId) (source : Modules.Source) (caller : State)
    (cache : List (Loader.ModuleId × Modules.Published)) (out : Modules.Result Unit) :
    Loader.Result Modules.Published :=
  match Modules.finish source caller out with
  | .error error final => .error (.initialization id error) ⟨final, cache⟩
  | .ok published final => .ok published ⟨final, (id, published) :: cache⟩

/-- A cache hit reuses the published value and the exact runtime heap. -/
inductive Producer (commands : List Command) (source : Modules.Source) :
    Session → Loader.Result Modules.Published → Prop where
  | cold {state : Session} {out : Modules.Result Unit} :
      state.cache.lookup 0 = none →
      ExecutesAll (Trace.names commands) (Modules.enter source state.runtime) commands out →
      Producer commands source state (observed 0 source state.runtime state.cache out)
  | cached {state : Session} {published : Modules.Published} :
      state.cache.lookup 0 = some published →
      Producer commands source state (.ok published state)

/-- Look up the requested name before any caller operand runs. -/
inductive BindsAlias (plan : Consumer) (published : Modules.Published) (state : State) :
    Modules.Result Unit → Prop where
  | missing : published.exports.lookup plan.name = none →
      BindsAlias plan published state (.error (.missingExport plan.label plan.name) state)
  | found {value : Lists.Value} : published.exports.lookup plan.name = some value →
      BindsAlias plan published state (.ok () (state.write (fileSlot plan.alias) value))

/-- The reached importer owns its import and declared globals in one frame. -/
@[expose] def Frame (alias : String) (globals : List String) (state : State) : Prop :=
  RootCall.DistinctOwned state ∧
    ∀ binding ∈ fileSlot alias :: globals.map globalSlot,
      ∃ address value frozen, state.slots binding = some (.owned address) ∧
        state.heap[address]? = some ⟨.binding value, frozen⟩

/-- Each tracked name reads a linked closure at the actual value in its slot.
The defining-frame witness stays with the closure when the caller changes. -/
@[expose] def Live (alias : String) (program : Program) (env : Environment) (state : State) : Prop :=
  ∀ name callee, env name = some callee →
    ∃ (slot address : Nat) (frozen : Bool) (defining : State),
      state.slots (readSlot alias name) = some (.owned slot) ∧
      state.heap[slot]? = some ⟨.binding (some (.function address)), frozen⟩ ∧
      callee.Linked program ∧ Nonempty (ClosureAt callee.site callee.id defining state address)

/-- Each importer statement uses the independent operand and call rules. -/
inductive Executes {alias : String} {globals : List String} (state : State) :
    Step alias globals → Modules.Result Unit → Prop where
  | assign {name declared source code reads} {operand : Body.Operand (block alias globals) source code reads}
      {copy : Copy alias source code} {out : Outcome Lists.Value} :
      Body.Evaluates (block alias globals) state source code out →
      Executes state (.assign name declared operand copy) (afterWrite name out)
  | invoke {call : Invocation alias globals} (callee : Callable) {out : Outcome Lists.Value} :
      RunsAt callee.site callee.BodyRuns (block alias globals) callee.id call.callee (readSlot alias call.callee)
        call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state out →
      Executes state (.invoke call) (afterWrite call.destination out)

/-- Stop at the first reached failure, keeping its exact residual heap. -/
inductive SuiteRuns {alias : String} {globals : List String} :
    State → List (Step alias globals) → Modules.Result Unit → Prop where
  | done (state : State) : SuiteRuns state [] (.ok () state)
  | next {state middle head rest out} :
      Executes state head (.ok () middle) → SuiteRuns middle rest out → SuiteRuns state (head :: rest) out
  | failed {state stopped head rest error} :
      Executes state head (.error error stopped) → SuiteRuns state (head :: rest) (.error error stopped)

inductive Runs (commands : List Command) (producer consumer : Modules.Source)
    (plan : Consumer) (exports : Environment) (caller : Session) :
    Loader.Result Modules.Published → Prop where
  | producerError {error : Loader.Error} {reached : Session} :
      Producer commands producer { caller with runtime := Modules.enter consumer caller.runtime }
        (.error error reached) →
      Runs commands producer consumer plan exports caller
        (.error error { reached with runtime := Modules.restoreThread caller.runtime reached.runtime })
  | missing {published : Modules.Published} {reached : Session} {error : Modules.Error} :
      Producer commands producer { caller with runtime := Modules.enter consumer caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.error error reached.runtime) →
      Runs commands producer consumer plan exports caller
        (observed 1 consumer caller.runtime reached.cache (.error error reached.runtime))
  | called {published : Modules.Published} {reached : Session} {bound : State}
      {callee : Callable} {out : Modules.Result Unit} :
      Producer commands producer { caller with runtime := Modules.enter consumer caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.ok () bound) →
      exports plan.name = some callee →
      SuiteRuns bound plan.body out →
      Runs commands producer consumer plan exports caller (observed 1 consumer caller.runtime reached.cache out)

abbrev Agrees (commands : List Command) (producer consumer : ResolvedModule)
    (plan : Consumer) (exports : Environment) (caller : Session) : Prop :=
  ∃ out, Runs commands producer.source consumer.source plan exports caller out ∧
    Loader.Runs producer.program (graph producer consumer plan) [] (.initialize 1) caller out ∧
    Loader.load producer.program (graph producer consumer plan) 1 caller = out

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
