module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Assignment (LexicalBlock)
open Functions
open Lists (State)
open Lists.Iteration (Flow)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

abbrev Bindings := List (Binding × Value)

abbrev Keywords := List (String × Value)

/-- Each explicit keyword is delivered to a named formal if one exists.
Unmatched values go to the keyword collector in encounter order. -/
inductive BindsNames (parameters : List Parameter) (kwargs : Option Binding) :
    Bindings × Keywords → Keywords → Except Lists.Error (Bindings × Keywords) → Prop where
  | done (bound : Bindings × Keywords) : BindsNames parameters kwargs bound [] (.ok bound)
  | unknown {bound : Bindings × Keywords} {name : String} {value : Value} {rest : Keywords} :
      kwargs = none →
      parameters.find? (fun formal => formal.slot.name == name) = none →
      BindsNames parameters kwargs bound ((name, value) :: rest) (.error (.unexpectedKeyword name))
  | conflict {bound : Bindings × Keywords} {name : String} {value previous : Value} {formal : Parameter}
      {rest : Keywords} :
      parameters.find? (fun item => item.slot.name == name) = some formal →
      List.lookup formal.slot bound.1 = some previous →
      BindsNames parameters kwargs bound ((name, value) :: rest) (.error (.multipleArgumentValues name))
  | deliver {bound : Bindings × Keywords} {name : String} {value : Value} {formal : Parameter}
      {rest : Keywords} {result : Except Lists.Error (Bindings × Keywords)} :
      parameters.find? (fun item => item.slot.name == name) = some formal →
      List.lookup formal.slot bound.1 = none →
      BindsNames parameters kwargs ((formal.slot, value) :: bound.1, bound.2) rest result →
      BindsNames parameters kwargs bound ((name, value) :: rest) result
  | repeated {bound : Bindings × Keywords} {name : String} {value previous : Value} {slot : Binding}
      {rest : Keywords} :
      kwargs = some slot →
      parameters.find? (fun item => item.slot.name == name) = none →
      List.lookup name bound.2 = some previous →
      BindsNames parameters kwargs bound ((name, value) :: rest) (.error (.multipleArgumentValues name))
  | collect {bound : Bindings × Keywords} {name : String} {value : Value} {slot : Binding}
      {rest : Keywords} {result : Except Lists.Error (Bindings × Keywords)} :
      kwargs = some slot →
      parameters.find? (fun item => item.slot.name == name) = none →
      List.lookup name bound.2 = none →
      BindsNames parameters kwargs (bound.1, bound.2 ++ [(name, value)]) rest result →
      BindsNames parameters kwargs bound ((name, value) :: rest) result

@[expose] def withDefaults (parameters : List Parameter) (bound saved : Bindings) :
    List (Binding × Option Value) :=
  parameters.map fun formal =>
    (formal.slot, (List.lookup formal.slot bound).orElse fun () => List.lookup formal.slot saved)

/-- The positional prefix has fixed capacity when no collector is present. -/
@[expose] def Fits (varargs : Option Binding) (parameters : List Parameter) (actual : Actual) : Prop :=
  varargs = none → actual.positional.length ≤ parameters.length

/-- Both surpluses are recorded during binding. Missing required
parameters reject before either collector can allocate. -/
inductive Binds (positional named : List Parameter) (varargs kwargs : Option Binding) (saved : Bindings)
    (actual : Actual) : Except Lists.Error BoundArguments → Prop where
  | surplus : varargs = none → positional.length < actual.positional.length →
      Binds positional named varargs kwargs saved actual (.error (.arity positional.length actual.positional.length))
  | rejected {error : Lists.Error} : Fits varargs positional actual →
      BindsNames named kwargs ((positional.map Parameter.slot).zip actual.positional, [])
        actual.keywords (.error error) →
      Binds positional named varargs kwargs saved actual (.error error)
  | missing {bound : Bindings} {extras : Keywords} : Fits varargs positional actual →
      BindsNames named kwargs ((positional.map Parameter.slot).zip actual.positional, [])
        actual.keywords (.ok (bound, extras)) →
      missingNames (withDefaults named bound saved) ≠ [] →
      Binds positional named varargs kwargs saved actual
        (.error (.missingArguments (missingNames (withDefaults named bound saved))))
  | assigned {bound : Bindings} {extras : Keywords} : Fits varargs positional actual →
      BindsNames named kwargs ((positional.map Parameter.slot).zip actual.positional, [])
        actual.keywords (.ok (bound, extras)) →
      missingNames (withDefaults named bound saved) = [] →
      Binds positional named varargs kwargs saved actual
        (.ok ⟨savedValues (withDefaults named bound saved),
          actual.positional.drop positional.length, extras⟩)

@[expose] def keywordEntries (keywords : Keywords) : List Lists.Entry :=
  keywords.map fun (name, value) => ⟨.string name, [.string name], value⟩

inductive PacksPositionals : Option Binding → State → BoundArguments → Bindings → State → Prop where
  | ordinary (caller : State) (bound : BoundArguments) : PacksPositionals none caller bound bound.named caller
  | tuple {slot : Binding} {caller packed : State} {bound : BoundArguments} {tuple : Value} :
      Lists.allocateTuple bound.surplusPositional caller = .ok tuple packed →
      PacksPositionals (some slot) caller bound ((slot, tuple) :: bound.named) packed

inductive PacksKeywords : Option Binding → State → Keywords → Bindings → Bindings → State → Prop where
  | ordinary (caller : State) (extras : Keywords) (assigned : Bindings) :
      PacksKeywords none caller extras assigned assigned caller
  | dict {slot : Binding} {caller packed : State} {extras : Keywords} {assigned : Bindings} {dictionary : Value} :
      Lists.allocateDict (keywordEntries extras) caller = .ok dictionary packed →
      PacksKeywords (some slot) caller extras assigned ((slot, dictionary) :: assigned) packed

/-- The positional pack precedes the keyword pack and both precede activation. -/
abbrev Packs (varargs kwargs : Option Binding) (caller : State) (bound : BoundArguments)
    (assigned : Bindings) (packed : State) : Prop :=
  ∃ positional middle, PacksPositionals varargs caller bound positional middle ∧
    PacksKeywords kwargs middle bound.surplusKeywords positional assigned packed

/-- Names are preserved by lexical operand resolution. -/
inductive Arguments (block : LexicalBlock) : List (String × Expr) →
    List (String × Lowering.Expr) → List Binding → Prop where
  | nil : Arguments block [] [] []
  | cons {name source code reads tail codes later} :
      Body.Operand block source code reads → Arguments block tail codes later →
      Arguments block ((name, source) :: tail) ((name, code) :: codes) (reads ++ later)

structure Operands (block : LexicalBlock) where
  source : List (String × Expr)
  codes : List (String × Lowering.Expr)
  reads : List Binding
  related : Arguments block source codes reads
  distinct : (source.map Prod.fst).Nodup

@[expose] def Operands.empty {block : LexicalBlock} : Operands block := ⟨[], [], [], .nil, .nil⟩

/-- Direct list and tuple displays supply elements whose checked operands
may read live references. An integer is admitted as a noniterable control. -/
inductive Spread (block : LexicalBlock) where
  | list {source : List Expr} {codes : List Lowering.Expr} {reads : List Binding} :
      Call.Arguments block source codes reads → Spread block
  | tuple {source : List Expr} {codes : List Lowering.Expr} {reads : List Binding} :
      Call.Arguments block source codes reads → Spread block
  | integer (value : Int) : Spread block

@[expose] def Spread.source {block : LexicalBlock} : Spread block → Expr
  | .list (source := source) _ => .list source
  | .tuple (source := source) _ => .tuple source
  | .integer value => .scalar (.int value)

@[expose] def Spread.code {block : LexicalBlock} : Spread block → Lowering.Expr
  | .list (codes := codes) _ => .list codes
  | .tuple (codes := codes) _ => .tuple codes
  | .integer value => .atom (.scalar (.int value))

@[expose] def Spread.reads {block : LexicalBlock} : Spread block → List Binding
  | .list (reads := reads) _ | .tuple (reads := reads) _ => reads
  | .integer _ => []

@[expose] def spreadReads {block : LexicalBlock} : Option (Spread block) → List Binding
  | none => []
  | some spread => spread.reads

/-- Evaluation is separate from expansion so a later mapping operand can fail first. -/
inductive EvaluatesSpread (block : LexicalBlock) : Option (Spread block) → State → Lists.Outcome (Option Value) → Prop where
  | absent (state : State) : EvaluatesSpread block none state (.ok none state)
  | list {source codes reads state out} {related : Call.Arguments block source codes reads} :
      Call.Evaluates block state source codes out →
      EvaluatesSpread block (some (.list related)) state
        (out.resume fun values reached =>
          Lists.Outcome.resume (Lists.allocate values reached) fun value allocated => .ok (some value) allocated)
  | tuple {source codes reads state out} {related : Call.Arguments block source codes reads} :
      Call.Evaluates block state source codes out →
      EvaluatesSpread block (some (.tuple related)) state
        (out.resume fun values reached =>
          Lists.Outcome.resume (Lists.allocateTuple values reached) fun value allocated => .ok (some value) allocated)
  | integer (state : State) (value : Int) :
      EvaluatesSpread block (some (.integer value)) state (.ok (some (.scalar (.int value))) state)

inductive ExpandsPositionals (state : State) : Option Value → Lists.Outcome (List Value) → Prop where
  | absent : ExpandsPositionals state none (.ok [] state)
  | list (address : Nat) : ExpandsPositionals state (some (.list address)) (Lists.listElements address state)
  | tuple (address : Nat) : ExpandsPositionals state (some (.tuple address)) (Lists.tupleElements address state)
  | invalid (value : Int) : ExpandsPositionals state (some (.scalar (.int value))) (.error .invalidStar state)

/-- Dictionary keys and values use the checked body operands and string literals. -/
inductive DisplayOperand (block : LexicalBlock) : Expr → Lowering.Expr → List Binding → Prop where
  | plain {source code reads} : Body.Operand block source code reads → DisplayOperand block source code reads
  | string (text : String) : DisplayOperand block (.string text) (.atom (.string text)) []

inductive DisplayEntries (block : LexicalBlock) :
    List (Expr × Expr) → List (Lowering.Expr × Lowering.Expr) → List Binding → Prop where
  | empty : DisplayEntries block [] [] []
  | entry {key value keyCode valueCode keyReads valueReads rest codes reads} :
      DisplayOperand block key keyCode keyReads → DisplayOperand block value valueCode valueReads →
      DisplayEntries block rest codes reads →
      DisplayEntries block ((key, value) :: rest) ((keyCode, valueCode) :: codes) (keyReads ++ valueReads ++ reads)

structure Mapping (block : LexicalBlock) where
  entries : List (Expr × Expr)
  codes : List (Lowering.Expr × Lowering.Expr)
  reads : List Binding
  related : DisplayEntries block entries codes reads

@[expose] def Mapping.source {block : LexicalBlock} (mapping : Mapping block) : Expr := .dict mapping.entries

@[expose] def Mapping.code {block : LexicalBlock} (mapping : Mapping block) : Lowering.Expr := .dict mapping.codes

@[expose] def mappingReads {block : LexicalBlock} (mapping : Option (Mapping block)) : List Binding :=
  (mapping.map Mapping.reads).getD []

inductive EvaluatesDisplayOperand (block : LexicalBlock) :
    State → Expr → Lowering.Expr → Lists.Outcome Value → Prop where
  | plain {state source code out} :
      Body.Evaluates block state source code out → EvaluatesDisplayOperand block state source code out
  | string (state : State) (text : String) :
      EvaluatesDisplayOperand block state (.string text) (.atom (.string text)) (.ok (.string text) state)

/-- Evaluate each key and value before attempting that pair's insertion. -/
inductive EvaluatesEntries (block : LexicalBlock) (address : Nat) :
    State → List (Expr × Expr) → List (Lowering.Expr × Lowering.Expr) → Lists.Outcome Unit → Prop where
  | empty (state : State) : EvaluatesEntries block address state [] [] (.ok () state)
  | keyError {state reached key value keyCode valueCode rest codes error} :
      EvaluatesDisplayOperand block state key keyCode (.error error reached) →
      EvaluatesEntries block address state ((key, value) :: rest) ((keyCode, valueCode) :: codes) (.error error reached)
  | valueError {state keyed reached key value keyCode valueCode rest codes k error} :
      EvaluatesDisplayOperand block state key keyCode (.ok k keyed) →
      EvaluatesDisplayOperand block keyed value valueCode (.error error reached) →
      EvaluatesEntries block address state ((key, value) :: rest) ((keyCode, valueCode) :: codes) (.error error reached)
  | insertionError {state keyed valued reached key value keyCode valueCode rest codes k v error} :
      EvaluatesDisplayOperand block state key keyCode (.ok k keyed) →
      EvaluatesDisplayOperand block keyed value valueCode (.ok v valued) →
      Lists.insertDisplayEntry (.dict address) k v valued = .error error reached →
      EvaluatesEntries block address state ((key, value) :: rest) ((keyCode, valueCode) :: codes) (.error error reached)
  | entry {state keyed valued inserted key value keyCode valueCode rest codes k v out} :
      EvaluatesDisplayOperand block state key keyCode (.ok k keyed) →
      EvaluatesDisplayOperand block keyed value valueCode (.ok v valued) →
      Lists.insertDisplayEntry (.dict address) k v valued = .ok () inserted →
      EvaluatesEntries block address inserted rest codes out →
      EvaluatesEntries block address state ((key, value) :: rest) ((keyCode, valueCode) :: codes) out

inductive EvaluatesMapping (block : LexicalBlock) :
    Option (Mapping block) → State → Lists.Outcome (Option Nat) → Prop where
  | absent (state : State) : EvaluatesMapping block none state (.ok none state)
  | dict {mapping state allocated out} :
      Lists.allocateDict [] state = .ok (.dict state.heap.size) allocated →
      EvaluatesEntries block state.heap.size allocated mapping.entries mapping.codes out →
      EvaluatesMapping block (some mapping) state (out.resume fun _ reached => .ok (some state.heap.size) reached)

/-- String validation retains the original value and scans in insertion order. -/
inductive KeywordEntries : List Lists.Entry → Except Lists.Error Keywords → Prop where
  | empty : KeywordEntries [] (.ok [])
  | string {key text value rest result} :
      KeywordEntries rest result →
      KeywordEntries (⟨.string text, key, value⟩ :: rest) (result.map ((text, value) :: ·))
  | nonString {key keyCode value rest} :
      (∀ text, key ≠ .string text) →
      KeywordEntries (⟨key, keyCode, value⟩ :: rest) (.error (.keywordMustBeString key))

inductive ExpandsMapping (state : State) : Option Nat → Lists.Outcome Keywords → Prop where
  | absent : ExpandsMapping state none (.ok [] state)
  | dict {address entries result} :
      Lists.dictEntries address state = .ok entries state → KeywordEntries entries result →
      ExpandsMapping state (some address) (Lists.fromExcept result state)
  | readError {address error} :
      Lists.dictEntries address state = .error error state →
      ExpandsMapping state (some address) (.error error state)


@[expose] def expressionAt (slot : Binding) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (star starStar : Option Lowering.Expr) : Lowering.Expr :=
  .call (Leaf.readOperand slot) positional keywords star starStar

@[expose] def expression (name : String) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (star starStar : Option Lowering.Expr := none) : Lowering.Expr :=
  expressionAt (fileSlot name) positional keywords star starStar

/-- The operand phase records both terminal carriers before validating either. -/
structure OperandValues where
  explicit : List Value
  star : Option Value
  mapping : Option Nat

inductive EvaluatesActualOperands (block : LexicalBlock) (source : List Expr) (codes : List Lowering.Expr)
    (star : Option (Spread block)) (mapping : Option (Mapping block)) :
    State → Lists.Outcome OperandValues → Prop where
  | explicitError {state final error} : Call.Evaluates block state source codes (.error error final) →
      EvaluatesActualOperands block source codes star mapping state (.error error final)
  | starError {state reached final values error} :
      Call.Evaluates block state source codes (.ok values reached) →
      EvaluatesSpread block star reached (.error error final) →
      EvaluatesActualOperands block source codes star mapping state (.error error final)
  | mappingError {state reached middle final values spread error} :
      Call.Evaluates block state source codes (.ok values reached) →
      EvaluatesSpread block star reached (.ok spread middle) →
      EvaluatesMapping block mapping middle (.error error final) →
      EvaluatesActualOperands block source codes star mapping state (.error error final)
  | ready {state reached middle final values spread dictionary} :
      Call.Evaluates block state source codes (.ok values reached) →
      EvaluatesSpread block star reached (.ok spread middle) →
      EvaluatesMapping block mapping middle (.ok dictionary final) →
      EvaluatesActualOperands block source codes star mapping state (.ok ⟨values, spread, dictionary⟩ final)

/-- Mapping string validation precedes positional expansion. Duplicate
argument names are still delivered to the binder in explicit-then-map order. -/
inductive ExpandsActuals (positional : Nat) (keywords : List String) (state : State) (values : OperandValues) :
    Lists.Outcome Actual → Prop where
  | badMapping {error final} : ExpandsMapping state values.mapping (.error error final) →
      ExpandsActuals positional keywords state values (.error error final)
  | badPositionals {named reached error final} :
      ExpandsMapping state values.mapping (.ok named reached) →
      ExpandsPositionals reached values.star (.error error final) →
      ExpandsActuals positional keywords state values (.error error final)
  | ready {named reached elements final} :
      ExpandsMapping state values.mapping (.ok named reached) →
      ExpandsPositionals reached values.star (.ok elements final) →
      ExpandsActuals positional keywords state values
        (.ok ⟨values.explicit.take positional ++ elements, keywords.zip (values.explicit.drop positional) ++ named⟩ final)

abbrev Actuals (block : LexicalBlock) (source : List Expr) (codes : List Lowering.Expr)
    (positional : Nat) (keywords : List String) (star : Option (Spread block)) (mapping : Option (Mapping block)) :=
  Call.ReachesActual (EvaluatesActualOperands block source codes star mapping)
    (fun state values => ExpandsActuals positional keywords state values)

abbrev SiteBinding {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope) : Call.BindingRule BoundArguments :=
  fun defaults => Binds site.declaration.signature.positional site.declaration.signature.named
    site.declaration.signature.varargs site.declaration.signature.kwargs (site.defaultKeys.zip defaults)

abbrev RunsAt {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope) (bodyRuns : State → Lists.Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (name : String) (slot : Binding)
    (arguments : List Expr) (codes : List Lowering.Expr) (keywords : List (String × Expr))
    (compiled : List (String × Lowering.Expr)) (star : Option (Spread block) := none)
    (mapping : Option (Mapping block) := none) :=
  Call.RunsActual site bodyRuns block id name slot
    (Actuals block (arguments ++ keywords.map Prod.snd) (codes ++ compiled.map Prod.snd)
      codes.length (compiled.map Prod.fst) star mapping)
    (SiteBinding site)
    (Packs site.declaration.signature.varargs site.declaration.signature.kwargs)

abbrev RunsWith {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) (bodyRuns : State → Lists.Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (name : String)
    (arguments : List Expr) (codes : List Lowering.Expr) (keywords : List (String × Expr))
    (compiled : List (String × Lowering.Expr)) (star : Option (Spread block) := none)
    (mapping : Option (Mapping block) := none) :=
  RunsAt site bodyRuns block id name (fileSlot name) arguments codes keywords compiled star mapping

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
