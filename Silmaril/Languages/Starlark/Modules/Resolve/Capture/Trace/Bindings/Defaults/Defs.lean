module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Functions
open Lists (State Outcome)
open Trace.Defaults (Definition)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

/-- The existing wrapper and mixed-leaf chains can coexist with a module
function that has positional defaults and returns one parameter. -/
inductive Callable where
  | required (chain : Forwarding.Chain)
  | defaulted (definition : Definition)
  | escaping (wrapper : Defaults.Escape.Spec)
  | sequenced (definition : Defaults.Body.Definition)
  | nestedBody (spec : Defaults.Escape.Scoped.Spec)

@[expose] def Callable.name : Callable → String
  | .required chain => chain.name
  | .defaulted definition => definition.name
  | .escaping wrapper => wrapper.name
  | .sequenced definition => definition.name
  | .nestedBody spec => spec.wrapper.name

@[expose] def Callable.command : Callable → Command
  | .required chain => root chain
  | .defaulted definition => definition.command
  | .escaping wrapper => wrapper.command
  | .sequenced definition => definition.command
  | .nestedBody spec => spec.command

@[expose] def Callable.Admitted (globals : List String) : Callable → Prop
  | .required chain => Trace.Definitions globals [] chain
  | .defaulted definition => Trace.Defaults.Admitted globals definition
  | .escaping wrapper => Defaults.Escape.Admitted wrapper
  | .sequenced definition => Defaults.Body.Admitted globals definition
  | .nestedBody spec => Defaults.Escape.Scoped.Admitted globals spec

@[expose] def Callable.returned : Callable → Option Callable
  | .required (.wrapper _ _ child) => some (.required child)
  | .required (.mixed ..) | .defaulted _ | .sequenced _ => none
  | .escaping wrapper => some (.defaulted wrapper.child)
  | .nestedBody spec => some (.sequenced spec.child)

abbrev Entries := String → Option Callable

@[expose] def Entries.write (entries : Entries) (name : String) (value : Option Callable) : Entries :=
  fun candidate => if candidate = name then value else entries candidate

/-- Static provenance advances through a successful definition, a direct
name copy, or a wrapper return. Call arguments are the existing bounded
read-only positional operands. -/
inductive Schedule (globals : List String) : Entries → List Command → Prop where
  | nil (entries : Entries) : Schedule globals entries []
  | define {entries : Entries} {body : Callable} {rest : List Command} :
      Visible globals body.name → body.Admitted globals →
      Schedule globals (entries.write body.name (some body)) rest →
      Schedule globals entries (body.command :: rest)
  | setup {entries : Entries} {name : String} {source : Expr} {rest : List Command} :
      Visible globals name → Initializer globals source → Schedule globals (entries.write name none) rest →
      Schedule globals entries (.assign name source :: rest)
  | copy {entries : Entries} {source destination : String} {body : Callable} {rest : List Command} :
      Visible globals source → Visible globals destination → entries source = some body →
      Schedule globals (entries.write destination (some body)) rest →
      Schedule globals entries (.assign destination (.scalar (.read source)) :: rest)
  | invoke {entries : Entries} {callee destination : String} {body : Callable}
      {arguments : List Expr} {rest : List Command} :
      Visible globals callee → Visible globals destination →
      entries callee = some body → (∀ argument ∈ arguments, Operand globals argument) →
      Schedule globals (entries.write destination body.returned) rest →
      Schedule globals entries (invocation callee destination arguments :: rest)

abbrev Profile (commands : List Command) : Prop := Schedule (names commands) (fun _ => none) commands

/-- The code table and runtime agree on a closure with saved positional
defaults. Aliases retain both its actual address and its saved values. -/
structure Saved (program : Program) (state : State) (name : String) (definition : Definition) where
  id : Nat
  codes : List Lowering.Expr
  address : Lists.Address
  values : List Value
  codeLength : codes.length = definition.parameters.optional.length
  valueLength : values.length = definition.parameters.optional.length
  found : program[id]? = some (definition.emitted codes)
  live : RootCall.Live state name address id [] false
    ((definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values)

/-- Both emitted declarations and the wrapper's actual runtime cell
stay linked through the remaining module commands. -/
structure Escaping (program : Program) (state : State) (name : String) (wrapper : Defaults.Escape.Spec) where
  childId : Nat
  address : Lists.Address
  admitted : Defaults.Escape.Admitted wrapper
  childCode : program[childId]? = some (wrapper.child.emitted wrapper.codes)
  parentCode : program[childId + 1]? = some (wrapper.frame childId).declaration
  live : RootCall.Live state name address (childId + 1) [] false

/-- A live body closure carries both the saved arguments and the
addresses installed for its independently selected free reads. -/
structure SavedBody (globals : List String) (program : Program) (state : State)
    (name : String) (definition : Defaults.Body.Definition) where
  id : Nat
  enclosing : List String
  plan : Defaults.Body.Plan globals definition enclosing
  codes : List Lowering.Expr
  address : Lists.Address
  values : List Value
  captures : List Lists.Capture
  codeLength : codes.length = definition.parameters.optional.length
  valueLength : values.length = definition.parameters.optional.length
  found : program[id]? = some (plan.declaration codes)
  owner : State
  installed : Installs owner plan.free captures
  cells : Defaults.Body.CaptureCells state captures
  live : RootCall.Live state name address id captures false
    ((definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values)

/-- The checked wrapper carries the exact compiled child plan. -/
structure ScopedRoot (globals : List String) (program : Program) (state : State) (name : String)
    (spec : Defaults.Escape.Scoped.Spec) where
  childId : Nat
  address : Lists.Address
  names : Defaults.Escape.WrapperNames spec.wrapper
  plan : Defaults.Escape.Scoped.Plan globals spec
  childCode : program[childId]? = some (plan.body.declaration spec.wrapper.codes)
  parentCode : program[childId + 1]? = some (spec.wrapper.frame childId).declaration
  live : RootCall.Live state name address (childId + 1) [] false

@[expose] def LiveBinding (globals : List String) (program : Program) (state : State)
    (name : String) : Callable → Prop
  | .required chain => Bindings.LiveBinding globals program state name chain
  | .defaulted definition => name ∈ globals ∧ Nonempty (Saved program state name definition)
  | .escaping wrapper => name ∈ globals ∧ Nonempty (Escaping program state name wrapper)
  | .sequenced definition => name ∈ globals ∧ Nonempty (SavedBody globals program state name definition)
  | .nestedBody spec => name ∈ globals ∧ Nonempty (ScopedRoot globals program state name spec)

@[expose] def LiveBindings (globals : List String) (program : Program) (entries : Entries) (state : State) : Prop :=
  ∀ name body, entries name = some body → LiveBinding globals program state name body

/-- Return reads the lexical parameter in the activation provided by
positional binding. The result keeps the exact heap after caller restore. -/
inductive ReturnsParameter (caller : State) (definition : Definition)
    (codes : List Lowering.Expr) (assigned : List (Binding × Value)) : Outcome Value → Prop where
  | read {value : Value}
      (read : (activate caller (definition.emitted codes) [] assigned).bindingValue (fileSlot definition.returned) = .ok value) :
      ReturnsParameter caller definition codes assigned
        (.ok value (restoreCaller caller (activate caller (definition.emitted codes) [] assigned)))
  | error {error : Lists.Error}
      (read : (activate caller (definition.emitted codes) [] assigned).bindingValue (fileSlot definition.returned) = .error error) :
      ReturnsParameter caller definition codes assigned
        (.error error (restoreCaller caller (activate caller (definition.emitted codes) [] assigned)))

/-- Independent source execution for an admitted call. The callee is read
before positional operands. Preparation starts only after all operands
succeed. The binder uses values saved at the closure's actual address. -/
inductive Calls (state : State) (definition : Definition) (codes : List Lowering.Expr) (saved : List Value)
    (arguments : List Expr) : Outcome Value → Prop where
  | rejected {actuals : List Value} {error : Lists.Error} :
      RootCall.EvaluatesOperands state arguments (.ok actuals state) →
      Trace.Defaults.Binds (definition.parameters.slots saved) actuals (.error error) →
      Calls state definition codes saved arguments (.error error state)
  | returned {actuals : List Value} {assigned : List (Binding × Value)} {out : Outcome Value} :
      RootCall.EvaluatesOperands state arguments (.ok actuals state) →
      Trace.Defaults.Binds (definition.parameters.slots saved) actuals (.ok assigned) →
      ReturnsParameter state definition codes assigned out →
      Calls state definition codes saved arguments out

/-- The wrapper has one required positional parameter. Only successful
binding reaches the nested definition and its local default reads. -/
inductive CallsWrapper (state : State) (wrapper : Defaults.Escape.Spec) (childId : Nat) :
    List Value → Outcome Value → Prop where
  | rejected {values : List Value} {error : Lists.Error} :
      Entry.Binds [wrapper.parameter] values (.error error) →
      CallsWrapper state wrapper childId values (.error error state)
  | entered {argument : Value} {out : Outcome Value} :
      Defaults.Escape.Returns wrapper childId state argument out →
      CallsWrapper state wrapper childId [argument] out

inductive CallsBody {globals : List String} {program : Program} {state : State} {name : String}
    {definition : Defaults.Body.Definition} (saved : SavedBody globals program state name definition)
    (values : List Value) : Outcome Value → Prop where
  | rejected {error : Lists.Error} :
      Defaults.Binds (definition.parameters.slots saved.values) values (.error error) →
      CallsBody saved values (.error error state)
  | entered {assigned : List (Binding × Value)} {out : Outcome Lists.Iteration.Flow} :
      Defaults.Binds (definition.parameters.slots saved.values) values (.ok assigned) →
      Defaults.Body.Runs saved.plan.block (activate state (saved.plan.declaration saved.codes) saved.captures assigned)
        definition.body saved.plan.code out →
      CallsBody saved values (Leaf.returnTo state out)

inductive CallsScoped (state : State) (wrapper : Defaults.Escape.Spec) (childId : Nat)
    (free : List FreeName) : List Value → Outcome Value → Prop where
  | rejected {values : List Value} {error : Lists.Error} :
      Entry.Binds [wrapper.parameter] values (.error error) →
      CallsScoped state wrapper childId free values (.error error state)
  | entered {argument : Value} {out : Outcome Value} :
      Defaults.Escape.ReturnsWith wrapper childId free state argument out →
      CallsScoped state wrapper childId free [argument] out

inductive Step (resolved : ResolvedModule) (globals : List String) :
    Nat → State → Command → Modules.Result Unit → Prop where
  | ordinary {index : Nat} {state : State} {command : Command} {out : Modules.Result Unit} :
      Leaf.Step resolved globals index state command out → Step resolved globals index state command out
  | definition {index : Nat} {state : State} {command : Command} {out : Modules.Result Unit} :
      Trace.Defaults.Step resolved globals index state command out → Step resolved globals index state command out
  | call {index : Nat} {state : State} {callee destination : String} {definition : Definition}
      {arguments : List Expr} {actuals : List Lowering.Expr} {out : Outcome Value}
      (saved : Saved resolved.program state callee definition) :
      resolved.source.commands[index]? =
        some (.exec (.assignExpr destination (.call (Leaf.readOperand (globalSlot callee)) actuals [] none none))) →
      RootCall.Operand globals (.scalar (.read callee)) (Leaf.readOperand (globalSlot callee)) →
      Assignment.InOrder (RootCall.Operand globals) arguments actuals →
      Calls state definition saved.codes saved.values arguments out →
      Step resolved globals index state (invocation callee destination arguments) (Leaf.assignResult destination out)
  | wrapper {index : Nat} {state : State} {callee destination : String} {body : Defaults.Escape.Spec}
      {arguments : List Expr} {actuals : List Lowering.Expr} {values : List Value} {out : Outcome Value}
      (root : Escaping resolved.program state callee body) :
      resolved.source.commands[index]? =
        some (.exec (.assignExpr destination (.call (Leaf.readOperand (globalSlot callee)) actuals [] none none))) →
      RootCall.Operand globals (.scalar (.read callee)) (Leaf.readOperand (globalSlot callee)) →
      Assignment.InOrder (RootCall.Operand globals) arguments actuals →
      RootCall.EvaluatesOperands state arguments (.ok values state) →
      CallsWrapper state body root.childId values out →
      Step resolved globals index state (invocation callee destination arguments) (Leaf.assignResult destination out)
  | bodyDefinition {index id : Nat} {state : State} {definition : Defaults.Body.Definition}
      {codes : List Lowering.Expr} {out : Outcome Lists.Iteration.Flow}
      (plan : Defaults.Body.Plan globals definition) :
      resolved.source.commands[index]? = some (.exec (.define definition.name id)) →
      resolved.program[id]? = some (plan.declaration codes) →
      codes.length = definition.parameters.optional.length →
      Defaults.Defines globals (globalSlot definition.name) id plan.free definition.parameters codes state out →
      Step resolved globals index state definition.command (Modules.afterCode out)
  | bodyCall {index : Nat} {state : State} {callee destination : String} {definition : Defaults.Body.Definition}
      {arguments : List Expr} {actuals : List Lowering.Expr} {values : List Value} {out : Outcome Value}
      (saved : SavedBody globals resolved.program state callee definition) :
      resolved.source.commands[index]? =
        some (.exec (.assignExpr destination (.call (Leaf.readOperand (globalSlot callee)) actuals [] none none))) →
      RootCall.Operand globals (.scalar (.read callee)) (Leaf.readOperand (globalSlot callee)) →
      Assignment.InOrder (RootCall.Operand globals) arguments actuals →
      RootCall.EvaluatesOperands state arguments (.ok values state) →
      CallsBody saved values out →
      Step resolved globals index state (invocation callee destination arguments) (Leaf.assignResult destination out)
  | scopedCall {index : Nat} {state : State} {callee destination : String} {spec : Defaults.Escape.Scoped.Spec}
      {arguments : List Expr} {actuals : List Lowering.Expr} {values : List Value} {out : Outcome Value}
      (root : ScopedRoot globals resolved.program state callee spec) :
      resolved.source.commands[index]? =
        some (.exec (.assignExpr destination (.call (Leaf.readOperand (globalSlot callee)) actuals [] none none))) →
      RootCall.Operand globals (.scalar (.read callee)) (Leaf.readOperand (globalSlot callee)) →
      Assignment.InOrder (RootCall.Operand globals) arguments actuals →
      RootCall.EvaluatesOperands state arguments (.ok values state) →
      CallsScoped state spec.wrapper root.childId root.plan.body.free values out →
      Step resolved globals index state (invocation callee destination arguments) (Leaf.assignResult destination out)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
