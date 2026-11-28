module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence.Recursive (Site KeywordLexical Emissions)
open Defaults.Nested.Sequence.Recursive.Call (ClosureAt Arguments)
open Defaults.Nested.Sequence.Recursive.Call.Suite (Runs)
open Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance (Elaborates Entry Returns empty)
open Defaults.Nested.Sequence (PreservesDeclarations)
open Functions
open Lists (State Outcome Capture)
open Lists.Iteration (Flow)

local notation "Expr" => Lowering.Resolve.SourceExpr

@[expose] def moduleLex (globals : List String) : LexicalBlock := ⟨[], [], globals⟩

/-- A root links the independent definition layout to the suite's ordered
emissions. Its own index follows those emitted by its body. -/
structure Root (globals : List String) where
  keywords : List PlainKeywordParameter
  varargs : Option String
  kwargs : Option String
  site : Site (moduleLex globals) keywords varargs kwargs .global
  lexical : KeywordLexical (moduleLex globals) keywords
  seed : Program
  bodyTable : Program
  children : Emissions
  returned : Option (Entry site.block) := none
  suite : Elaborates site.block empty site.source seed site.body bodyTable children returned

@[expose] def Root.command {globals : List String} (root : Root globals) : Command :=
  .define root.site.name root.site.sourceSignature root.site.source

@[expose] def Root.id {globals : List String} (root : Root globals) : DeclarationId := root.bodyTable.size

@[expose] def Root.table {globals : List String} (root : Root globals) : Program :=
  root.bodyTable.push root.site.declaration

/-- A callable's source declaration and expected return shape. Its
runtime address is supplied by the reached binding, never by this certificate. -/
structure Callable where
  parent : LexicalBlock
  scope : Scope
  keywords : List PlainKeywordParameter
  varargs : Option String
  kwargs : Option String
  site : Site parent keywords varargs kwargs scope
  id : DeclarationId
  returned : Option (Entry site.block)

@[expose] def Root.callable {globals : List String} (root : Root globals) : Callable :=
  ⟨moduleLex globals, .global, root.keywords, root.varargs, root.kwargs, root.site, root.id, root.returned⟩

@[expose] def Callable.nested {block : LexicalBlock} (entry : Entry block) : Callable :=
  ⟨block, .local, entry.formals, entry.varargs, entry.kwargs, entry.site, entry.id, none⟩

@[expose] def Callable.Linked (callee : Callable) (program : Program) : Prop :=
  program[callee.id]? = some callee.site.declaration ∧
    ∃ seed bodyTable children, bodyTable.size = callee.id ∧ PreservesDeclarations bodyTable program ∧
      Elaborates callee.site.block empty callee.site.source seed callee.site.body bodyTable children callee.returned

abbrev Callable.BodyRuns (callee : Callable) (active : State) (out : Outcome Flow) : Prop :=
  Runs callee.site.block active callee.site.source callee.site.body.code out ∧ Returns callee.returned out

abbrev Environment := String → Option Callable

@[expose] def update (env : Environment) (name : String)
    (entry : Option Callable) : Environment :=
  fun candidate => if candidate = name then entry else env candidate

/-- Ordinary expressions clear the destination's provenance. An explicit
copy transfers the callable certificate without assuming the closure's address. -/
inductive Tracks (env : Environment) :
    Expr → Lowering.Expr → Option Callable → Prop where
  | forget {source code} : Tracks env source code none
  | copy {name : String} {root : Callable} :
      env name = some root →
      Tracks env (.scalar (.read name)) (Leaf.readOperand (globalSlot name)) (some root)

structure Invocation (globals : List String) where
  callee : String
  calleeGlobal : callee ∈ globals
  legal : callee.toList.head? ≠ some '$'
  destination : String
  destinationGlobal : destination ∈ globals
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments (moduleLex globals) arguments codes reads
  keywords : Defaults.Nested.Sequence.Recursive.Call.Named.Operands (moduleLex globals)
  star : Option (Defaults.Nested.Sequence.Recursive.Call.Named.Spread (moduleLex globals)) := none
  mapping : Option (Defaults.Nested.Sequence.Recursive.Call.Named.Mapping (moduleLex globals)) := none

open Defaults.Nested.Sequence.Recursive.Call.Named (Spread Mapping expressionAt RunsAt)

@[expose] def Invocation.source {globals : List String} (call : Invocation globals) : Command :=
  .assign call.destination (.call (.scalar (.read call.callee)) call.arguments call.keywords.source
    (call.star.map Spread.source) (call.mapping.map Mapping.source))

@[expose] def Invocation.code {globals : List String} (call : Invocation globals) : Lowering.Expr :=
  expressionAt (globalSlot call.callee) call.codes call.keywords.codes
    (call.star.map Spread.code) (call.mapping.map Mapping.code)

/-- The load-free schedule threads declaration tables and provenance in
source order. Ordinary assignments and calls can be interleaved. -/
inductive Plan (globals : List String) :
    Environment → List Command → Program → List Modules.Command → Program → Environment → Prop where
  | done {env seed} : Plan globals env [] seed [] seed env
  | define {env source code final exports} (root : Root globals) :
      Plan globals (update env root.site.name (some root.callable)) source root.table code final exports →
      Plan globals env (root.command :: source) root.seed (.exec (.define root.site.name root.id) :: code) final exports
  | assign {env name source code reads track rest next seed final exports} :
      name ∈ globals → Body.Operand (moduleLex globals) source code reads →
      Tracks env source code track → Plan globals (update env name track) rest seed next final exports →
      Plan globals env (.assign name source :: rest) seed (.exec (.assignExpr name code) :: next) final exports
  | invoke {env rest next seed final exports} (call : Invocation globals) (callee : Callable) :
      env call.callee = some callee →
      Plan globals (update env call.destination (callee.returned.map Callable.nested)) rest seed next final exports →
      Plan globals env (call.source :: rest) seed (.exec (.assignExpr call.destination call.code) :: next) final exports

/-- Tracked module names point at records in the reached shared heap.
An activation can read captured module slots even when they are uninitialized. -/
@[expose] def Live (env : Environment) (state : State) : Prop :=
  ∀ name callee, env name = some callee →
    ∃ address defining, state.bindingValue (globalSlot name) = .ok (.function address) ∧
      Nonempty (ClosureAt callee.site callee.id defining state address)

/-- Public tracked exports retain their declaration link and the original
closure record. Publication freezes the record without changing its contents. -/
@[expose] def PublishedLive (env : Environment) (program : Program) (published : Modules.Published)
    (state : State) : Prop :=
  ∀ name callee, env name = some callee → Modules.isPublic name = true →
    callee.Linked program ∧
    ∃ address defining, published.exports.lookup name = some (.function address) ∧
      ∃ record : ClosureAt callee.site callee.id defining state address, record.frozen = true

@[expose] def resultState {α : Type} : Modules.Result α → State
  | .ok _ state | .error _ state => state

/-- Publication may freeze a caller cell. Its address and contents survive. -/
@[expose] def KeepsContents (before after : State) : Prop :=
  ∀ (address : Nat) (cell : Lists.Cell), before.heap[address]? = some cell →
    ∃ frozen, after.heap[address]? = some { cell with frozen }

@[expose] def afterWrite (name : String) : Outcome Lists.Value → Modules.Result Unit
  | .error error state => .error (.runtime error) state
  | .ok value state => .ok () (state.write (globalSlot name) value)

inductive Executes (globals : List String) : State → Command → Modules.Result Unit → Prop where
  | define {state : State} (root : Root globals) (captures : List Capture) {out : Outcome Flow} :
      Installs state root.site.free captures →
      Lexical.DefinesFor (moduleLex globals) (globalSlot root.site.name) root.id root.site.free
        root.site.defaultKeys root.site.defaultsInOrder state out →
      Executes globals state root.command (Modules.afterCode out)
  | assign {state name source code out} :
      Body.Evaluates (moduleLex globals) state source code out →
      Executes globals state (.assign name source) (afterWrite name out)
  | invoke {state out} (call : Invocation globals) (callee : Callable) :
      RunsAt callee.site callee.BodyRuns
        (moduleLex globals) callee.id call.callee (globalSlot call.callee)
        call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state out →
      Executes globals state call.source (afterWrite call.destination out)

/-- Stop at the first reached error, retaining its exact state. -/
inductive ExecutesAll (globals : List String) : State → List Command → Modules.Result Unit → Prop where
  | done (state : State) : ExecutesAll globals state [] (.ok () state)
  | step {state middle first rest out} :
      Executes globals state first (.ok () middle) → ExecutesAll globals middle rest out →
      ExecutesAll globals state (first :: rest) out
  | failed {state final first rest error} :
      Executes globals state first (.error error final) → ExecutesAll globals state (first :: rest) (.error error final)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
