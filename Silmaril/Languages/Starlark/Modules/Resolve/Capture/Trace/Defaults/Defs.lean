module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open Functions
open Lists (State Outcome Capture)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

/-- A source positional signature has a required prefix and a defaulted
suffix. The existing module validator checks distinct parameter names. -/
structure Parameters where
  required : List String
  optional : List (String × Expr)

@[expose] def Parameters.names (parameters : Parameters) : List String :=
  parameters.required ++ parameters.optional.map Prod.fst

@[expose] def Parameters.source (parameters : Parameters) : SourceSignature :=
  { positional := parameters.required.map (fun name => ⟨name, none⟩) ++
      parameters.optional.map fun (name, expr) => ⟨name, some (.plain expr)⟩ }

@[expose] def Parameters.signature (parameters : Parameters) (codes : List Lowering.Expr) : Signature :=
  let optional := ((parameters.optional.map (fileSlot ∘ Prod.fst)).zip codes).map
    (fun (slot, code) => (⟨slot, some code⟩ : Parameter))
  { positional := (requiredSignature parameters.required).positional ++ optional }

/-- The source definition bridge starts with a body that returns one
parameter. The binder theorem below applies to arbitrary resolved bodies. -/
structure Definition where
  name : String
  parameters : Parameters
  returned : String

@[expose] def Definition.command (definition : Definition) : Command :=
  .define definition.name definition.parameters.source (.ret (some (.scalar (.read definition.returned))))

/-- The definition-site profile uses only the existing read-only setup
operands and allocation-only list and tuple displays. -/
structure Admitted (globals : List String) (definition : Definition) : Prop where
  defaults : ∀ item ∈ definition.parameters.optional, Initializer globals item.2
  returned : Visible definition.parameters.names definition.returned

@[expose] def Definition.emitted (definition : Definition) (codes : List Lowering.Expr) : Declaration :=
  { signature := definition.parameters.signature codes
    locals := []
    free := []
    body := .returnExpr (Leaf.readOperand (fileSlot definition.returned)) }

/-- The source rules evaluate the admitted expressions in the defining
state before the new function is put in its destination. A reached error
has no premise for any subsequent expression. -/
inductive Evaluates (globals : List String) :
    State → List Expr → List Lowering.Expr → Outcome (List Value) → Prop where
  | nil {state : State} : Evaluates globals state [] [] (.ok [] state)
  | next {state middle : State} {first : Expr} {code : Lowering.Expr} {value : Value}
      {rest : List Expr} {codes : List Lowering.Expr} {out : Outcome (List Value)} :
      Leaf.Setup globals state first code (.ok value middle) →
      Evaluates globals middle rest codes out →
      Evaluates globals state (first :: rest) (code :: codes)
        (out.resume fun values final => .ok (value :: values) final)
  | error {state final : State} {first : Expr} {code : Lowering.Expr} {rest : List Expr}
      {codes : List Lowering.Expr} {error : Lists.Error} :
      Leaf.Setup globals state first code (.error error final) →
      Evaluates globals state (first :: rest) (code :: codes) (.error error final)

/-- On success the saved values, including mutable aliases, are stored
directly in the function cell. Only then does the definition bind its name. -/
@[expose] def install (target : Binding) (id : Nat) (captures : List Capture)
    (defaults : List (Binding × Value)) (state : State) : State :=
  { state with heap := state.heap.push ⟨.function ⟨id, captures, defaults⟩, false⟩ }.write
    target (.function state.heap.size)

/-- Source definition effects, including the residual state of a failed default. -/
inductive Defines (globals : List String) (target : Binding) (id : Nat) (free : List FreeName)
    (parameters : Parameters) (codes : List Lowering.Expr) :
    State → Outcome Lists.Iteration.Flow → Prop where
  | failed {state final : State} {error : Lists.Error} :
      Evaluates globals state (parameters.optional.map Prod.snd) codes (.error error final) →
      Defines globals target id free parameters codes state (.error error final)
  | installed {state final : State} {values : List Value} {captures : List Capture} :
      Evaluates globals state (parameters.optional.map Prod.snd) codes (.ok values final) →
      Installs final free captures →
      Defines globals target id free parameters codes state
        (.ok .next (install target id captures ((parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) final))

/-- A reached module command is either a setup assignment or the bounded
definition. Calls with saved defaults are covered at the binder boundary. -/
inductive Step (resolved : ResolvedModule) (globals : List String) :
    Nat → State → Command → Modules.Result Unit → Prop where
  | setup {index : Nat} {state : State} {name : String} {source : Expr} {code : Lowering.Expr}
      {out : Outcome Value} :
      resolved.source.commands[index]? = some (.exec (.assignExpr name code)) →
      Leaf.Setup globals state source code out →
      Step resolved globals index state (.assign name source) (Leaf.assignResult name out)
  | define {index id : Nat} {state : State} {definition : Definition} {codes : List Lowering.Expr}
      {out : Outcome Lists.Iteration.Flow} :
      resolved.source.commands[index]? = some (.exec (.define definition.name id)) →
      resolved.program[id]? = some (definition.emitted codes) →
      codes.length = definition.parameters.optional.length →
      Defines globals (globalSlot definition.name) id [] definition.parameters codes state out →
      Step resolved globals index state definition.command (Modules.afterCode out)

/-- One bounded positional definition surrounded by allocation-only and
read-only setup assignments. -/
structure ModuleProfile (before after : List Command) (definition : Definition) : Prop where
  beforeSetup : Tail (names (before ++ definition.command :: after)) before
  afterSetup : Tail (names (before ++ definition.command :: after)) after
  definitionAllowed : Admitted (names (before ++ definition.command :: after)) definition

/-- An independent walk over the declared slots. Explicit operands replace
a saved value when present. Once operands run out, the suffix is reused. -/
@[expose] def fill : List (Binding × Option Value) → List Value → List (Binding × Option Value)
  | [], _ => []
  | slots, [] => slots
  | (slot, _) :: rest, value :: values => (slot, some value) :: fill rest values

@[expose] def savedValues (slots : List (Binding × Option Value)) : List (Binding × Value) :=
  slots.filterMap fun (slot, value) => (value.map fun found => (slot, found))

@[expose] def missingNames (slots : List (Binding × Option Value)) : List String :=
  slots.filterMap fun (slot, value) => if value.isNone then some slot.name else none

/-- Binding a call consults saved values. It has no evaluation premise and
does not allocate a frame on an arity or missing-argument failure. -/
inductive Binds (slots : List (Binding × Option Value)) (values : List Value) :
    Except Lists.Error (List (Binding × Value)) → Prop where
  | surplus : slots.length < values.length →
      Binds slots values (.error (.arity slots.length values.length))
  | missing : values.length ≤ slots.length → missingNames (fill slots values) ≠ [] →
      Binds slots values (.error (.missingArguments (missingNames (fill slots values))))
  | assigned : values.length ≤ slots.length → missingNames (fill slots values) = [] →
      Binds slots values (.ok (savedValues (fill slots values)))

/-- The saved closure entries list exactly the optional slots in
declaration order. Required slots have no saved value. -/
@[expose] def Parameters.slots (parameters : Parameters) (values : List Value) :
    List (Binding × Option Value) :=
  parameters.required.map (fun name => (fileSlot name, none)) ++
    (parameters.optional.map (fileSlot ∘ Prod.fst)).zip (values.map some)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
