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

/-- The display is evaluated once. Expansion transports the exact original
element values in order and leaves the display's reached state intact. -/
inductive Spreads (block : LexicalBlock) : Option (Spread block) → State → Lists.Outcome (List Value) → Prop where
  | absent (state : State) : Spreads block none state (.ok [] state)
  | list {source codes reads state out} {related : Call.Arguments block source codes reads} :
      Call.Evaluates block state source codes out →
      Spreads block (some (.list related)) state
        (out.resume fun values reached =>
          Lists.Outcome.resume (Lists.allocate values reached) fun _ allocated => .ok values allocated)
  | tuple {source codes reads state out} {related : Call.Arguments block source codes reads} :
      Call.Evaluates block state source codes out →
      Spreads block (some (.tuple related)) state
        (out.resume fun values reached =>
          Lists.Outcome.resume (Lists.allocateTuple values reached) fun _ allocated => .ok values allocated)
  | invalid (state : State) (value : Int) : Spreads block (some (.integer value)) state (.error .invalidStar state)

@[expose] def expression (name : String) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (star : Option Lowering.Expr := none) : Lowering.Expr :=
  .call (Leaf.readOperand (fileSlot name)) positional keywords star none

/-- The flattened successful operand values are partitioned by the
syntactic positional count and paired with the original keyword names. -/
@[expose] def collect (positional : Nat) (keywords : List String) (values : List Value) (spread : List Value := []) : Actual :=
  ⟨values.take positional ++ spread, keywords.zip (values.drop positional)⟩

/-- The terminal spread runs after explicit operands and before binding. -/
inductive Actuals (block : LexicalBlock) (source : List Expr) (codes : List Lowering.Expr)
    (positional : Nat) (keywords : List String) (star : Option (Spread block)) :
    State → Lists.Outcome Actual → Prop where
  | operandError {state final error} : Call.Evaluates block state source codes (.error error final) →
      Actuals block source codes positional keywords star state (.error error final)
  | spreadError {state reached final values error} :
      Call.Evaluates block state source codes (.ok values reached) →
      Spreads block star reached (.error error final) →
      Actuals block source codes positional keywords star state (.error error final)
  | expanded {state reached final values elements} :
      Call.Evaluates block state source codes (.ok values reached) →
      Spreads block star reached (.ok elements final) →
      Actuals block source codes positional keywords star state (.ok (collect positional keywords values elements) final)

abbrev SiteBinding {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) : Call.BindingRule BoundArguments :=
  fun defaults => Binds site.declaration.signature.positional site.declaration.signature.named
    site.declaration.signature.varargs site.declaration.signature.kwargs (site.defaultKeys.zip defaults)

abbrev RunsWith {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) (bodyRuns : State → Lists.Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (name : String)
    (arguments : List Expr) (codes : List Lowering.Expr) (keywords : List (String × Expr))
    (compiled : List (String × Lowering.Expr)) (star : Option (Spread block) := none) :=
  Call.RunsActual site bodyRuns block id name
    (Actuals block (arguments ++ keywords.map Prod.snd) (codes ++ compiled.map Prod.snd)
      codes.length (compiled.map Prod.fst) star)
    (SiteBinding site)
    (Packs site.declaration.signature.varargs site.declaration.signature.kwargs)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
