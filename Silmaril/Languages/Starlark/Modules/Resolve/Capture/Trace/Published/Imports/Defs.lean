module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Loader.Operational.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence (PreservesDeclarations)
open Defaults.Nested.Sequence.Recursive (Site)
open Defaults.Nested.Sequence.Recursive.Call (Arguments ClosureAt)
open Lists.Iteration (Flow)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping Operands RunsAt Spread expressionAt spreadReads mappingReads)
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

/-- An importer declaration returns a checked call through the immutable
file-local import. Its only capture is that binding's address. -/
structure WrapperDeclaration (alias : String) (globals : List String) where
  name : String
  target : name ∈ globals
  legalAlias : alias.toList.head? ≠ some '$'
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments ⟨[], [alias], globals⟩ arguments codes reads
  keywords : Operands ⟨[], [alias], globals⟩
  star : Option (Spread ⟨[], [alias], globals⟩) := none
  mapping : Option (Mapping ⟨[], [alias], globals⟩) := none
  selects : Selects ⟨[], [alias], globals⟩
    (fileSlot alias :: (reads ++ keywords.reads ++ spreadReads star ++ mappingReads mapping))
    [⟨fileSlot alias, fileSlot alias⟩]

@[expose] def WrapperDeclaration.expression {alias globals} (relay : WrapperDeclaration alias globals) : Expr :=
  .call (.scalar (.read alias)) relay.arguments relay.keywords.source
    (relay.star.map Spread.source) (relay.mapping.map Mapping.source)

@[expose] def WrapperDeclaration.code {alias globals} (relay : WrapperDeclaration alias globals) : Lowering.Expr :=
  expressionAt (fileSlot alias) relay.codes relay.keywords.codes (relay.star.map Spread.code) (relay.mapping.map Mapping.code)

@[expose] def WrapperDeclaration.site {alias globals} (relay : WrapperDeclaration alias globals) : Site (block alias globals) [] none none .global where
  name := relay.name
  target := relay.target
  parameters := ⟨[], []⟩
  source := .ret (some relay.expression)
  binders := []
  locals := []
  collects := .ret _
  localOrder := .nil
  body := ⟨.returnExpr relay.code, fileSlot alias ::
    (relay.reads ++ relay.keywords.reads ++ spreadReads relay.star ++ mappingReads relay.mapping)⟩
  free := [⟨fileSlot alias, fileSlot alias⟩]
  selects := relay.selects
  defaults := []
  lexical := .nil

/-- An independent return rule for a call through the captured import. -/
@[expose] def WrapperDeclaration.Returns {alias globals} (relay : WrapperDeclaration alias globals) (callee : Callable)
    (active : State) (out : Outcome Flow) : Prop :=
  ∃ result, RunsAt callee.site callee.BodyRuns relay.site.block callee.id alias (fileSlot alias)
      relay.arguments relay.codes relay.keywords.source relay.keywords.codes relay.star relay.mapping active result ∧
    out = result.resume (fun value => pure (.returned value))

inductive Callee (alias : String) (globals : List String) where
  | regular (callee : Callable)
  | wrapper (declaration : WrapperDeclaration alias globals) (id : DeclarationId)

@[expose] def Callee.layout {alias globals} : Callee alias globals → Callable
  | .regular callee => callee
  | .wrapper declaration id => ⟨block alias globals, .global, [], none, none, declaration.site, id, none⟩

@[expose] def Callee.BodyRuns {alias globals} (imported : Callable) :
    Callee alias globals → State → Outcome Flow → Prop
  | .regular callee => callee.BodyRuns
  | .wrapper declaration _ => declaration.Returns imported

@[expose] def Callee.returned {alias globals} (imported : Callable) :
    Callee alias globals → Option (Callee alias globals)
  | .regular callee => callee.returned.map (Callee.regular ∘ Callable.nested)
  | .wrapper .. => imported.returned.map (Callee.regular ∘ Callable.nested)

@[expose] def Callee.Linked {alias globals} (producer final : Program) : Callee alias globals → Prop
  | .regular callee => callee.Linked producer
  | .wrapper declaration id => producer.size ≤ id ∧ final[id]? = some declaration.site.declaration

/-- The wrapper is created in this module frame and retains its load slot
through copies and calls. Ordinary callables keep their own defining frame. -/
@[expose] def Callee.SharesImport {alias globals} :
    Callee alias globals → (Binding → Option Lists.Slot) → (Binding → Option Lists.Slot) → Prop
  | .regular _, _, _ => True
  | .wrapper .., defining, current => defining (fileSlot alias) = current (fileSlot alias)

abbrev Tracked (alias : String) (globals : List String) := String → Option (Callee alias globals)

@[expose] def track {alias globals} (env : Tracked alias globals) (name : String)
    (entry : Option (Callee alias globals)) : Tracked alias globals :=
  fun read => if read = name then entry else env read

/-- A checked name copy propagates the original callable. Other assignments
forget the destination's previous provenance. -/
inductive Copy (alias : String) : Expr → Lowering.Expr → Type where
  | forget {source code} : Copy alias source code
  | name (name : String) : Copy alias (.scalar (.read name)) (Leaf.readOperand (readSlot alias name))

@[expose] def Copy.track {alias globals source code} (copy : Copy alias source code) (env : Tracked alias globals) : Option (Callee alias globals) :=
  match copy with
  | .forget => none
  | .name read => env read

inductive Step (alias : String) (globals : List String) where
  | assign (destination : String) (declared : destination ∈ globals) {source : Expr}
      {code : Lowering.Expr} {reads : List Binding} :
      Body.Operand (block alias globals) source code reads → Copy alias source code → Step alias globals
  | invoke (call : Invocation alias globals)
  | define (declaration : WrapperDeclaration alias globals)

@[expose] def Step.destination {alias globals} : Step alias globals → String
  | .assign name .. => name
  | .invoke call => call.destination
  | .define declaration => declaration.name

@[expose] def Step.source {alias globals} : Step alias globals → Command
  | .assign name _ (source := source) _ _ => .assign name source
  | .invoke call => .assign call.destination call.source
  | .define declaration => .define declaration.name declaration.site.sourceSignature declaration.site.source

@[expose] def Step.code {alias globals} (program : Program) : Step alias globals → Modules.Command
  | .assign name _ (code := code) _ _ => .exec (.assignExpr name code)
  | .invoke call => .exec (.assignExpr call.destination call.code)
  | .define declaration => .exec (.define declaration.name program.size)

@[expose] def Step.emit {alias globals} (program : Program) : Step alias globals → Program
  | .define declaration => program.push declaration.site.declaration
  | _ => program

@[expose] def Step.advance {alias globals} (imported : Callable) (program : Program) (env : Tracked alias globals) :
    Step alias globals → Tracked alias globals
  | .assign destination _ _ copy => track env destination (copy.track env)
  | .invoke call =>
    track env call.destination ((env call.callee).bind (Callee.returned imported))
  | .define declaration => track env declaration.name (some (.wrapper declaration program.size))

@[expose] def compileSuite {alias globals} (program : Program) :
    List (Step alias globals) → List Modules.Command × Program
  | [] => ([], program)
  | head :: tail =>
    let compiled := compileSuite (head.emit program) tail
    (head.code program :: compiled.1, compiled.2)

@[expose] def trackSuite {alias globals} (imported : Callable) (program : Program) (env : Tracked alias globals) :
    List (Step alias globals) → Tracked alias globals
  | [] => env
  | head :: tail => trackSuite imported (head.emit program) (head.advance imported program env) tail

/-- Source-order provenance enables each call and describes the destination
after its successful return. Declaration IDs follow the current table. -/
@[expose] def ReadyFor {alias : String} {globals : List String} (imported : Callable) (program : Program)
    (env : Tracked alias globals) : List (Step alias globals) → Prop
  | [] => True
  | first :: rest =>
    let tail := ReadyFor imported (first.emit program) (first.advance imported program env) rest
    match first with
    | .invoke call => ∃ callee, env call.callee = some callee ∧ tail
    | _ => tail

/-- The consumer declares one renamed public import and a finite suite.
The globals are collected from the suite's definition and assignment targets. -/
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

@[expose] def Consumer.code (plan : Consumer) (program : Program) : List Modules.Command :=
  .load plan.label [plan.item] :: (compileSuite program plan.body).1

@[expose] def initial {globals : List String} (alias : String) (callee : Callable) : Tracked alias globals :=
  track (fun _ => none) alias (some (.regular callee))

/-- Producer zero has no dependencies. Consumer one has just the one
requester-relative label. Both use the final linked table. -/
@[expose] def graph (producer consumer : ResolvedModule) (plan : Consumer) : Manifest :=
  #[⟨producer.source, []⟩, ⟨consumer.source, [(plan.label, 0)]⟩]

/-- The source profile tracks either a producer export or a name outside the
producer's declared globals. The consumer supplies no declaration or address. -/
@[expose] def Covered (exports : Environment) (producer : List Command) (plan : Consumer) (program : Program) : Prop :=
  (∃ callee, exports plan.name = some callee ∧ ReadyFor callee program (initial plan.alias callee) plan.body) ∨
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

/-- Importer writes use the cells allocated by the current module entry. -/
@[expose] def FreshSlots (floor : Nat) (state : State) : Prop :=
  ∀ binding address, state.slots binding = some (.owned address) → floor ≤ address

/-- Binding writes preserve function records and keep capture addresses
allocated as binding cells. Exact contents for earlier owners use FreshSlots. -/
structure KeepsClosureCells (before after : State) : Prop where
  functions : ∀ (address : Nat) closure flag, before.heap[address]? = some ⟨.function closure, flag⟩ →
    ∃ next, after.heap[address]? = some ⟨.function closure, next⟩
  bindings : ∀ (address : Nat) value flag, before.heap[address]? = some ⟨.binding value, flag⟩ →
    ∃ next frozen, after.heap[address]? = some ⟨.binding next, frozen⟩

/-- Each tracked name reads a linked closure at the actual value in its slot.
The defining-frame witness stays with the closure when the caller changes. -/
@[expose] def Live (alias : String) {globals : List String} (producer final : Program)
    (env : Tracked alias globals) (state : State) : Prop :=
  ∀ name callee, env name = some callee →
    ∃ (slot address : Nat) (frozen : Bool) (defining : State),
      state.slots (readSlot alias name) = some (.owned slot) ∧
      state.heap[slot]? = some ⟨.binding (some (.function address)), frozen⟩ ∧ callee.Linked producer final ∧
      Nonempty (ClosureAt callee.layout.site callee.layout.id defining state address) ∧
      callee.SharesImport defining.slots state.slots

/-- Each importer statement uses the independent operand, definition and call rules. -/
inductive Executes {alias : String} {globals : List String} (imported : Callable)
    (program : Program) (state : State) : Step alias globals → Modules.Result Unit → Prop where
  | assign {name declared source code reads} {operand : Body.Operand (block alias globals) source code reads}
      {copy : Copy alias source code} {out : Outcome Lists.Value} :
      Body.Evaluates (block alias globals) state source code out →
      Executes imported program state (.assign name declared operand copy) (afterWrite name out)
  | define {declaration : WrapperDeclaration alias globals} {out : Outcome Flow} :
      Lexical.DefinesFor (block alias globals) (globalSlot declaration.name) program.size declaration.site.free [] [] state out →
      Executes imported program state (.define declaration) (Modules.afterCode out)
  | invoke {call : Invocation alias globals} (callee : Callee alias globals) {out : Outcome Lists.Value} :
      RunsAt callee.layout.site (callee.BodyRuns imported) (block alias globals) callee.layout.id call.callee (readSlot alias call.callee)
        call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state out →
      Executes imported program state (.invoke call) (afterWrite call.destination out)

/-- Stop at the first reached failure, keeping its exact residual heap. -/
inductive SuiteRuns {alias : String} {globals : List String} (imported : Callable) :
    Program → State → List (Step alias globals) → Modules.Result Unit → Prop where
  | done (program : Program) (state : State) : SuiteRuns imported program state [] (.ok () state)
  | next {program state middle head rest out} :
      Executes imported program state head (.ok () middle) →
      SuiteRuns imported (head.emit program) middle rest out →
      SuiteRuns imported program state (head :: rest) out
  | failed {program state stopped head rest error} :
      Executes imported program state head (.error error stopped) →
      SuiteRuns imported program state (head :: rest) (.error error stopped)

inductive Runs (commands : List Command) (producer consumer : ResolvedModule)
    (plan : Consumer) (exports : Environment) (caller : Session) :
    Loader.Result Modules.Published → Prop where
  | producerError {error : Loader.Error} {reached : Session} :
      Producer commands producer.source { caller with runtime := Modules.enter consumer.source caller.runtime }
        (.error error reached) →
      Runs commands producer consumer plan exports caller
        (.error error { reached with runtime := Modules.restoreThread caller.runtime reached.runtime })
  | missing {published : Modules.Published} {reached : Session} {error : Modules.Error} :
      Producer commands producer.source { caller with runtime := Modules.enter consumer.source caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.error error reached.runtime) →
      Runs commands producer consumer plan exports caller
        (observed 1 consumer.source caller.runtime reached.cache (.error error reached.runtime))
  | called {published : Modules.Published} {reached : Session} {bound : State}
      {callee : Callable} {out : Modules.Result Unit} :
      Producer commands producer.source { caller with runtime := Modules.enter consumer.source caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.ok () bound) →
      exports plan.name = some callee →
      SuiteRuns callee producer.program bound plan.body out →
      Runs commands producer consumer plan exports caller (observed 1 consumer.source caller.runtime reached.cache out)

abbrev Agrees (commands : List Command) (producer consumer : ResolvedModule)
    (plan : Consumer) (exports : Environment) (caller : Session) : Prop :=
  ∃ out, Runs commands producer consumer plan exports caller out ∧
    Loader.Runs consumer.program (graph producer consumer plan) [] (.initialize 1) caller out ∧
    Loader.load consumer.program (graph producer consumer plan) 1 caller = out

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
