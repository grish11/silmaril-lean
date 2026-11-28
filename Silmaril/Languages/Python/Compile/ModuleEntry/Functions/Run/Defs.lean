module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain.Eval.Defs

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Defs
public import Silmaril.Languages.Python.Compile.Closure.Run.Defs
public import Silmaril.Languages.Python.Compile.Closure.VarNames.Defs
public import Silmaril.Languages.Python.Core.Module.Functions.Defs

/-! # Run lowered module bindings and calls -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

open Source (Scope)
open Compile.Closure (frameLayout)
open Core.Closure (CodeRef Frame Heap Layout RuntimeError Slot Value)
open Core.Closure.Executor (Body CodeTable Event)
open Core.Module.Functions (Invocation Session TopFunction)

inductive Argument where
  | scalar (operand : Core.Module.Functions.Operand)
  | dictionaryGet (test : Core.Module.Dictionary.Get)
  | dictionaryDisplay (entries : List Core.Module.Dictionary.Entry)
  | call (name : String) (arguments : List Core.Module.Functions.Operand)

inductive Instruction (scope : Scope) where
  | scalar (action : ModuleEntry.Action scope)
  | exceptionalTry (plan : ExceptionalTry.Plan (ExceptionalTry.Step scope))
  | bindText (name : String) (value : Core.Text)
  | bindDictionary (name : String) (display : List Core.Module.Dictionary.Entry)
  | readDictionary (name : String) (test : Core.Module.Dictionary.Get)
  | clearDictionary (destination : Option String) (call : Core.Module.Dictionary.Clear)
  | bindTuple (name : String) (items : List Core.Closure.GlobalTupleItem) (trackClosed : Bool := false)
  | assertNot (condition : Operand scope)
  | assertIntegerBuiltin (test : IntegerBuiltinTest scope)
  | assertBoolIdentity (test : BoolIdentityTest scope)
  | assertListConstruction (test : ListConstructionTest scope)
  | assertTupleChain (test : TupleChainTest scope)
  | textSliceGuard (test : TextSlice.Guard)
  | assertVarNames (receiver : String) (needle : List UInt32)
  | publish (name : String) (function : TopFunction)
  | call (destination : Core.Module.Functions.Destination) (name : String) (operands : List Core.Module.Functions.Operand)
  | callTupleIdentity (destination : Core.Module.Functions.Destination) (name : String) (test : TupleIdentity.Test)
  | callTupleFromListDisplay (destination : Core.Module.Functions.Destination) (contents : List Core.Module.Value)
      (outer : Option (String × List Argument))
  | callListDisplay (destination : Core.Module.Functions.Destination) (name : String)
      (display : ListDisplay.Display)
  /-- The source plan places this call immediately after the matching publication. -/
  | adjacentKeywordDiscard (name : String) (value : Int)
  | nestedCall (destination : Core.Module.Functions.Destination) (name : String) (arguments : List Argument)

abbrev Instruction.assertSequenceLength {scope : Scope} (test : SequenceLengthTest scope) : Instruction scope :=
  .assertIntegerBuiltin test.toIntegerBuiltin

inductive CompileError where
  | source (error : Functions.Error)
  | incomingCaptures (path : Source.BlockPath)
  | functionBody (error : Compile.Closure.Run.Error)
  | callOperand
  deriving Repr

def callOperand? {scope : Scope} : Operand scope → Option Core.Module.Functions.Operand
  | .integer value => some (.literal (.int value))
  | .boolean value => some (.literal (.bool value))
  | .read name _ => some (.readGlobal name)
  | .binary .equal (.boolean left) (.boolean right) => some (.literal (.bool (left == right)))
  | .none_ | .binary .. | .identityChain .. => none

def callValue? {scope : Scope} : CallValue scope → Option Core.Module.Functions.Operand
  | .scalar operand => callOperand? operand
  | .intDivMod op numerator divisor => some (.intDivMod op numerator divisor)
  | .intTrueDiv numerator divisor => some (.intTrueDiv numerator divisor)
  | .floatDivMod op operands => some (.floatDivMod op operands)
  | .floatDiv operands => some (.floatDiv operands)
  | .mixedAdd integer floating => some (.mixedAdd integer floating)
  | .floatAdd left right => some (.floatAdd left right)
  | .floatSub operands => some (.floatSub operands)
  | .floatMul operands => some (.floatMul operands)
  | .float64 value => some (.literal (.float64 value))
  | .tuple items => some (.tuple items)
  | .text value => some (.literal (.text value))
  | .textSlice receiver bounds => some (.textSlice receiver bounds)

def callArgument? {scope : Scope} : CallArgument scope → Option Argument
  | .dictionaryGet test => some (.dictionaryGet test)
  | .dictionaryDisplay entries => some (.dictionaryDisplay entries)
  | .value (.scalar .none_) => some (.scalar (.literal .none))
  | .value operand => (callValue? operand).map .scalar
  | .call name _ operands => (operands.mapM callValue?).map (.call name)

def destination {scope : Scope} : Functions.Destination scope → Core.Module.Functions.Destination
  | .discard => .discard
  | .store name _ => .bindGlobal name
  | .assertion => .assert

/-- The literal belongs to the function's linked entry. The zero-positional
binder must succeed before this store initializes the keyword-only local. -/
def initializeKeywordDefault {layout : Layout} (code : Compile.Closure.Body.Code layout) :
    Option (Fin layout.locals × Int) → Compile.Closure.Body.Code layout
  | none => code
  | some (slot, value) => .assign (.local slot) (.integer value) code

def lowerInstructions {scope : Scope} (tree : Source.ScopeTree) (next : Nat) : List (Functions.Action scope) →
    Except CompileError (List (Instruction scope) × List Compile.Closure.Link.Block)
  | [] => .ok ([], [])
  | .scalar action :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.scalar action :: instructions, blocks)
  | .exceptionalTry plan :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.exceptionalTry plan :: instructions, blocks)
  | .bindText name _ value :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.bindText name value :: instructions, blocks)
  | .bindDictionary name _ display :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.bindDictionary name display :: instructions, blocks)
  | .readDictionary name _ test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.readDictionary name test :: instructions, blocks)
  | .clearDictionary destination call :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.clearDictionary destination call :: instructions, blocks)
  | .bindTuple name _ items :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.bindTuple name items :: instructions, blocks)
  | .assertNot condition :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.assertNot condition :: instructions, blocks)
  | .assertIntegerBuiltin test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.assertIntegerBuiltin test :: instructions, blocks)
  | .assertBoolIdentity test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.assertBoolIdentity test :: instructions, blocks)
  | .assertListConstruction test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.assertListConstruction test :: instructions, blocks)
  | .assertTupleChain test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.assertTupleChain test :: instructions, blocks)
  | .textSliceGuard test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.textSliceGuard test :: instructions, blocks)
  | .assertVarNames receiver _ needle :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.assertVarNames receiver needle :: instructions, blocks)
  | .call target name _ operands :: rest => do
    let some arguments := operands.mapM callOperand? | throw .callOperand
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.call (destination target) name arguments :: instructions, blocks)
  | .callTupleIdentity target name _ test :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.callTupleIdentity (destination target) name test :: instructions, blocks)
  | .callTupleFromListDisplay target name _ contents arguments :: rest => do
    let some outer := arguments.mapM (fun rest => (rest.mapM callArgument?).map (name, ·)) | throw .callOperand
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.callTupleFromListDisplay (destination target) contents outer :: instructions, blocks)
  | .callListDisplay target name _ display :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.callListDisplay (destination target) name display :: instructions, blocks)
  | .adjacentKeywordDiscard name _ value :: rest => do
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.adjacentKeywordDiscard name value :: instructions, blocks)
  | .nestedCall target name _ operands :: rest => do
    let some arguments := operands.mapM callArgument? | throw .callOperand
    let (instructions, blocks) ← lowerInstructions tree next rest
    return (.nestedCall (destination target) name arguments :: instructions, blocks)
  | .define name _ child parameters code keywordDefault :: rest => do
    let layout := frameLayout child.scope
    if captures : layout.captures = 0 then
      let nested := Compile.Closure.Link.linkBody (next + 1) tree (initializeKeywordDefault code keywordDefault)
      let (instructions, blocks) ← lowerInstructions tree (next + 1 + nested.children.length) rest
      let root : Compile.Closure.Link.Block :=
        ⟨child.scope.context.path, ⟨layout, { parameters, body := nested.code }⟩⟩
      let profiled := match keywordDefault with
        | none => ((root.withFreeVars tree).withCellVars tree).withCodeNames tree
        | some _ => root
      return (.publish name ⟨⟨next, layout⟩, captures⟩ :: instructions,
        profiled :: (nested.children ++ blocks))
    else throw (.incomingCaptures child.scope.context.path)

def Instruction.observesTupleIdentity {scope : Scope} : Instruction scope → Bool
  | .callTupleIdentity .. => true
  | _ => false

/-- Only modules observing tuple identity need a witness for closed
nonempty tuples. Bindings, aliases, and calls share the same carrier. -/
def retainTupleOrigins {scope : Scope} (instructions : List (Instruction scope)) : List (Instruction scope) :=
  if instructions.any Instruction.observesTupleIdentity then
    instructions.map fun
      | .bindTuple name items _ => .bindTuple name items true
      | instruction => instruction
  else instructions

structure Compiled (source : Source.Module) where
  checked : Functions.Checked source
  instructions : List (Instruction checked.tree.scope)
  linked : List Compile.Closure.Link.Block
  entries : List Compile.Closure.Run.ExecutorEntry
  lowered : Compile.Closure.Run.TableTranslation linked entries

def Compiled.table {source : Source.Module} (compiled : Compiled source) : CodeTable :=
  fun key => compiled.entries[key]?

def compile (source : Source.Module) : Except CompileError (Compiled source) := do
  let checked ← (Functions.check source).mapError .source
  let (instructions, blocks) ← lowerInstructions checked.tree 0 checked.actions
  let linked := Compile.Closure.VarNames.attach checked.tree blocks
  let table ← (Compile.Closure.Run.lowerTable linked).mapError .functionBody
  return ⟨checked, retainTupleOrigins instructions, linked, table.val, table.property⟩

def embed : Core.Module.Value → Value
  | .int value => .int value
  | .bool value => .bool value
  | .none => .none

def seed (globals : Core.Module.Globals) (heap : Heap := .empty) : Session :=
  ⟨fun name => (globals.lookup name).map embed, heap, .empty⟩

inductive Completion where
  | normal
  | raised (error : RuntimeError)
  | assertionError
  | codeFault (error : Core.Closure.Dispatch.Failure)
  | executorFault (error : Core.Closure.Executor.Fault)
  | scalarProfile
  | unprofiledVarNames (ref : CodeRef)
  | unsupportedVarNamesReceiver
  deriving DecidableEq, Repr

def tupleBinding (session : Session) : Option Core.Module.TupleDispatch.TypeBinding :=
  (session.globals "tuple").map fun
    | .none => .noneValue
    | .int _ | .bool _ | .float64 _ | .text _ | .tuple _ | .tupleObject _
    | .exceptionInstance _ | .dictionary _ | .dictionaryData _ => .nonCallable
    | .exceptionClass _ | .function _ => .outsideProfile

def tupleLookup (session : Session) : TupleChain.Lookup :=
  ⟨fun _ => tupleBinding session, fun name => (session.globals name).map TupleChain.Compared.ofClosure⟩

def checkTupleChain {scope : Scope} (session : Session) (test : TupleChainTest scope) : Except Completion Unit :=
  match (TupleChain.evaluate (tupleLookup session) test).result with
  | .ok true => .ok ()
  | .ok false => .error .assertionError
  | .error error => .error ((TupleChain.runtimeError? error).elim .scalarProfile .raised)

def checkTextSliceGuard (session : Session) (test : TextSlice.Guard) : Except Completion Unit :=
  (test.eval session.globals (fun
    | .text value => some value
    | _ => none)).mapError fun
      | .missingName name => .raised (.nameError name)
      | .zeroStep => .raised .zeroSliceStep
      | .outsideTextProfile | .reachedRaise => .scalarProfile

def scalar? : Value → Option Core.Module.Value := Value.scalar?

def evaluate {scope : Scope} (session : Session) : Operand scope → Except Completion Value
  | .integer value => .ok (.int value)
  | .boolean value => .ok (.bool value)
  | .none_ => .ok .none
  | .read name _ =>
    match session.globals name with
    | some value => .ok value
    | none => .error (.raised (.nameError name))
  | .binary op lhs rhs => do
    let first ← evaluate session lhs
    let second ← evaluate session rhs
    let some left := scalar? first | throw .scalarProfile
    let some right := scalar? second | throw .scalarProfile
    match (ModuleEntry.Run.operator op).eval left right with
    | .ok value => .ok (embed value)
    | .error (.arithmetic error) => .error (.raised (.arithmetic error))
    | .error (.nameError name) => .error (.raised (.nameError name))
    | .error .assertionError => .error .assertionError
    | .error .unsupportedArithmetic => .error .scalarProfile
    | .error .unsupportedIdentity => .error .scalarProfile
  | .identityChain left links =>
    let singleton value := (scalar? value).bind Core.Module.Value.singleton?
    (Core.Module.Identity.project singleton .scalarProfile (evaluate session left)).bind fun first =>
      (Core.Module.Identity.scan first (links.attach.map fun link =>
        (link.val.1, fun _ => Core.Module.Identity.project singleton .scalarProfile (evaluate session link.val.2)))).map .bool
termination_by operand => sizeOf operand
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := Core.Module.Identity.sizeOf_operand_lt link.property
      omega

def Argument.emit {layout : Layout} (destination : Fin layout.locals) (next : Body layout) :
    Argument → Body layout
  | .scalar operand => .store (.local destination) operand.lower next
  | .dictionaryGet test => .store (.local destination) (.dictionaryGet test) next
  | .dictionaryDisplay entries => .storeDictionary destination entries next
  | .call name arguments => .call (.local destination) (.readGlobal name)
      (arguments.map Core.Module.Functions.Operand.lower) next

/-- Save the outer callable first and evaluate each argument once in source
order. The scratch slots are private to this frame and use no shared cells. -/
def prepareNestedCall (session : Session) (destination : Core.Module.Functions.Destination)
    (name : String) (arguments : List Argument) : Invocation :=
  let layout : Layout := ⟨arguments.length + 2, 0, 0⟩
  let callee : Slot layout := .local ⟨0, by change 0 < arguments.length + 2; omega⟩
  let result : Slot layout := .local ⟨1, by change 1 < arguments.length + 2; omega⟩
  let slots : List (Fin layout.locals) := (List.finRange arguments.length).map fun i =>
    ⟨i.val + 2, Nat.add_lt_add_right i.isLt 2⟩
  let invoke := Body.call result (.read callee) (slots.map fun slot => .read (.local slot)) (.ret (.read result))
  let body := (slots.zip arguments).foldr (fun (slot, argument) next => argument.emit slot next) invoke
  let frame : Frame layout := ⟨fun _ => none, Fin.elim0, Fin.elim0⟩
  ⟨session.globals, destination, .running session.heap frame (.store callee (.readGlobal name) body) [], session.lists⟩

inductive State (scope : Scope) where
  | ready (session : Session) (instructions : List (Instruction scope))
  | calling (invocation : Invocation) (remaining : List (Instruction scope))
  | finished (session : Session) (completion : Completion)

def checkAssertion {scope : Scope} (session : Session) (operand : Operand scope)
    (expectedTruth : Bool) : Except Completion Unit :=
  (evaluate session operand).bind fun value =>
    if Core.Module.Functions.truth value session.heap = expectedTruth then .ok () else .error .assertionError

def assertOperand {scope : Scope} (session : Session) (operand : Operand scope)
    (expectedTruth : Bool) (remaining : List (Instruction scope)) : State scope :=
  match checkAssertion session operand expectedTruth with
  | .ok () => .ready session remaining
  | .error error => .finished session error

def scalarStep {scope : Scope} (session : Session) : ModuleEntry.Action scope → Except Completion Session
  | .assign name _ operand => (evaluate session operand).map (session.bindGlobal name)
  | .assertion operand => (checkAssertion session operand true).map fun _ => session

def Completion.isPythonError : Completion → Bool
  | .raised _ | .assertionError => true
  | _ => false

def raiseValue : Value → ExceptionalTry.RaiseValue
  | .exceptionClass kind => .stockClass kind
  | .exceptionInstance value => .exceptionInstance value
  | .function _ => .otherCallable
  | _ => .nonCallable

def raiseText? : Value → Option Core.Text
  | .text text => some text
  | _ => none

def exceptionalStep {scope : Scope} (session : Session) : ExceptionalTry.Step scope → Except Completion Session
  | .scalar action => scalarStep session action
  | .raiseName operand => .error (.raised (operand.error session.globals raiseValue))
  | .raiseCall call => .error ((call.error session.globals raiseValue raiseText?).elim .scalarProfile .raised)
  | .raiseInactive => .error (.raised .noActiveException)

def handlerClass : Value → ExceptionalTry.HandlerClass
  | .exceptionClass kind => .stock kind
  | .tuple _ | .tupleObject _ => .outsideProfile
  | _ => .invalid

def matchHandler (session : Session) (error : Completion) (name : String) : Except Completion Bool :=
  let matchType actual :=
    (ExceptionalTry.matchClass session.globals handlerClass actual name).mapError
      (fun failure => failure.elim .scalarProfile .raised)
  match error with
  | .assertionError => matchType .assertionError
  | .raised raised => matchType raised.classify
  | _ => .error .scalarProfile

def Completion.handlerInstance? : Completion → Option Core.Closure.ExceptionInstance
  | .assertionError => some (.empty .assertionError)
  | .raised error => error.handlerInstance?
  | _ => none

def bindCaught (session : Session) (name : String) (pending : Completion) : Except Completion Session :=
  pending.handlerInstance?.elim (.error .scalarProfile) fun value =>
    .ok (session.bindGlobal name (.exceptionInstance value))

def handlerOperations : ExceptionalTry.HandlerOperations Session Completion :=
  ⟨matchHandler, bindCaught, Session.unbindGlobal⟩

def runExceptionalTry {scope : Scope} (session : Session) (plan : ExceptionalTry.Plan (ExceptionalTry.Step scope)) :
    ExceptionalTry.Outcome Session Completion :=
  ExceptionalTry.run (ExceptionalTry.runSuite exceptionalStep) Completion.isPythonError handlerOperations session plan

inductive VarNamesFailure where
  | unsupportedReceiver
  | unprofiled (ref : CodeRef)
  | code (error : Core.Closure.Dispatch.Failure)

/-- Test the checked tuple of an already resolved receiver. Namespace lookup
and assertion completion belong to the calling module runner. -/
def varNamesMembership (table : CodeTable) (value : Value)
    (needle : List UInt32) : Except VarNamesFailure Bool := do
  let .function function := value | throw .unsupportedReceiver
  let definition ← (Core.Closure.Dispatch.resolve table function.code).mapError .code
  let some names := definition.varnames | throw (.unprofiled function.code)
  return names.any (fun name => name.toList.map Char.val == needle)

/-- Inspect the code of the current module binding without calling it.
This profile uses the ordinary module namespace with no builtin fallback. -/
def checkVarNames (table : CodeTable) (session : Session) (receiver : String)
    (needle : List UInt32) : Except Completion Unit := do
  let some value := session.globals receiver | throw (.raised (.nameError receiver))
  let member ← (varNamesMembership table value needle).mapError fun
    | .unsupportedReceiver => .unsupportedVarNamesReceiver
    | .unprofiled ref => .unprofiledVarNames ref
    | .code error => .codeFault error
  unless member do throw .assertionError

/-- The ordinary namespace has no stock descriptor. Read the name and then
prepare the argument before classifying a present mask. -/
def boolIdentityCompletion {scope : Scope} (session : Session) (test : BoolIdentityTest scope) : Completion :=
  match session.globals "bool" with
  | none => .raised (.nameError "bool")
  | some callee =>
    match test.argument.mapM (evaluate session) with
    | .error error => error
    | .ok _ =>
      match callee with
      | .exceptionClass _ | .function _ => .scalarProfile
      | _ => .raised .notCallable

def evaluateTuple (session : Session) (items : List Core.Closure.GlobalTupleItem) :
    Except Core.Closure.Failure (List Core.Module.TupleDispatch.Element) :=
  let frame : Frame ⟨0, 0, 0⟩ := ⟨Fin.elim0, Fin.elim0, Fin.elim0⟩
  Core.Closure.Executor.evalTupleContentsIn session.globals session.heap frame items

def bindDictionary (session : Session) (name : String) (display : List Core.Module.Dictionary.Entry) : Session :=
  let (object, heap) := session.heap.materializeDictionary display
  { session.bindGlobal name (.dictionary object) with heap }

def operandFailure : Core.Closure.Failure → Completion
  | .defined error => .raised error
  | .danglingCell identity => .executorFault (.danglingCell identity)
  | .unsupportedTupleElement => .executorFault .unsupportedTupleElement
  | .unsupportedFloatOperand => .executorFault .unsupportedFloatOperand
  | .unsupportedDictionaryOperand => .executorFault .unsupportedDictionaryOperand
  | .unsupportedCallable => .executorFault .unsupportedCallable

def bindTuple (session : Session) (name : String) (items : List Core.Closure.GlobalTupleItem)
    (trackClosed : Bool := false) : Except Completion Session :=
  match evaluateTuple session items with
  | .ok contents =>
    let (value, heap) := session.heap.materializeModuleTuple items contents trackClosed
    .ok ({ session with heap := heap }.bindGlobal name value)
  | .error error => .error (operandFailure error)

def prepareTupleIdentityCall (session : Session) (destination : Core.Module.Functions.Destination)
    (name : String) (test : TupleIdentity.Test) : Except Completion Invocation := do
  let read name := (session.globals name).elim (.error (.raised (.nameError name))) (fun value => .ok value)
  let callee ← read name
  let answer ← test.evaluate session.heap (fun name => (read name).map some) .scalarProfile
  return session.prepareCall destination (.literal callee) [.literal (.bool answer)]

/-- The ordinary namespace has no stock tuple descriptor. A reached
literal still allocates before a present callee is rejected. -/
def tupleFromListDisplayCompletion (session : Session) (contents : List Core.Module.Value)
    (outer : Option (String × List Argument)) : Completion × Core.Module.ListHeap :=
  if let some (name, _) := outer then
    if (session.globals name).isNone then
      (.raised (.nameError name), session.lists)
    else reachedDisplay
  else reachedDisplay
where
  reachedDisplay :=
    let (result, reached) := Core.Module.TupleDispatch.constructFromListDisplay session.lists (tupleBinding session) contents
    let completion := match result with
      | .ok _ => .scalarProfile
      | .error error => (TupleChain.runtimeError? error).elim .scalarProfile .raised
    (completion, reached)

def readListItem (session : Session) (name : String) : Except Completion Core.Module.Value := do
  let some value := session.globals name | throw (.raised (.nameError name))
  let some scalar := scalar? value | throw .scalarProfile
  return scalar

def advanceListDisplayCall {scope : Scope} (session : Session) (destination : Core.Module.Functions.Destination)
    (name : String) (display : ListDisplay.Display) (rest : List (Instruction scope)) : State scope :=
  match session.globals name with
  | none => .finished session (.raised (.nameError name))
  | some callee =>
    let (result, lists) := display.prepare (readListItem session) session.lists
    let reached := { session with lists }
    match result with
    | .error error => .finished reached error
    | .ok object =>
      if display.negated then
        .calling (reached.prepareCall destination (.literal callee) [.literal (.bool object.contents.isEmpty)]) rest
      else
        .finished reached (match callee with
          | .exceptionClass _ | .function _ => .scalarProfile
          | _ => .raised .notCallable)

def advance {scope : Scope} (table : CodeTable) : State scope → List Event × State scope
  | .finished session completion => ([], .finished session completion)
  | .ready session [] => ([], .finished session .normal)
  | .ready session (instruction :: rest) =>
    match instruction with
    | .scalar action => ([], match scalarStep session action with
      | .ok reached => .ready reached rest
      | .error error => .finished session error)
    | .exceptionalTry plan =>
      let outcome := runExceptionalTry session plan
      ([], match outcome.completion with
        | .ok () => .ready outcome.reached rest
        | .error error => .finished outcome.reached error)
    | .bindText name value => ([], .ready (session.bindGlobal name (.text value)) rest)
    | .bindDictionary name display => ([], .ready (bindDictionary session name display) rest)
    | .readDictionary name test => ([], match Core.Closure.evalDictionaryGet session.heap session.globals test with
      | .ok value => .ready (session.bindGlobal name value) rest
      | .error error => .finished session (operandFailure error))
    | .clearDictionary destination call =>
      match Core.Closure.clearDictionary session.heap (fun name => (session.globals name).map Value.dictionaryRead) call with
      | .ok heap =>
        let reached := { session with heap }
        let bound := destination.elim reached fun name => reached.bindGlobal name .none
        ([.complete (.ok .none)], .ready bound rest)
      | .error error =>
        let events := match error with
          | .clearArity actual => [.complete (.error (.positionalArity 0 actual))]
          | _ => []
        (events, .finished session (operandFailure (Core.Closure.dictionaryFailure error)))
    | .bindTuple name items trackClosed => ([], match bindTuple session name items trackClosed with
      | .ok updated => .ready updated rest
      | .error error => .finished session error)
    | .assertNot operand => ([], assertOperand session operand false rest)
    | .assertIntegerBuiltin test => ([], .finished session (match session.globals test.argument.name with
      | none => .raised (.nameError test.argument.name)
      | some (.exceptionClass _) | some (.function _) => .scalarProfile
      | some _ => .raised .notCallable))
    | .assertBoolIdentity test => ([], .finished session (boolIdentityCompletion session test))
    | .assertListConstruction _ => ([], .finished session (match session.globals "list" with
      | none => .raised (.nameError "list")
      | some (.exceptionClass _) | some (.function _) => .scalarProfile
      | some _ => .raised .notCallable))
    | .assertTupleChain test => ([], match checkTupleChain session test with
      | .ok () => .ready session rest
      | .error error => .finished session error)
    | .textSliceGuard test => ([], match checkTextSliceGuard session test with
      | .ok () => .ready session rest
      | .error error => .finished session error)
    | .assertVarNames receiver needle => ([], match checkVarNames table session receiver needle with
      | .ok () => .ready session rest
      | .error completion => .finished session completion)
    | .publish name function => ([], match session.publish table name function with
      | .ok updated => .ready updated rest
      | .error fault => .finished session (.codeFault fault))
    | .call destination name arguments => ([], .calling (session.prepareCall destination (.readGlobal name) arguments) rest)
    | .callTupleIdentity destination name test =>
      ([], match prepareTupleIdentityCall session destination name test with
        | .ok invocation => .calling invocation rest
        | .error error => .finished session error)
    | .callTupleFromListDisplay _ contents outer =>
      let (completion, lists) := tupleFromListDisplayCompletion session contents outer
      ([], .finished { session with lists } completion)
    | .callListDisplay destination name display =>
      ([], advanceListDisplayCall session destination name display rest)
    | .adjacentKeywordDiscard name value =>
      ([], .calling (session.prepareCall .discard (.readGlobal name) [.literal (.int value)]) rest)
    | .nestedCall destination name arguments =>
      ([], .calling (prepareNestedCall session destination name arguments) rest)
  | .calling invocation rest =>
    let (log, residual) := invocation.runPrefix table 1
    (log, match residual.finish? with
      | none => .calling residual rest
      | some observation => match observation.completion with
        | .returned _ => .ready observation.residual rest
        | .raised error => .finished observation.residual (.raised error)
        | .assertionError => .finished observation.residual .assertionError
        | .fault fault => .finished observation.residual (.executorFault fault))

def runPrefix {scope : Scope} (table : CodeTable) : Nat → State scope → List Event × State scope
  | 0, state => ([], state)
  | _ + 1, .finished session completion => ([], .finished session completion)
  | fuel + 1, state =>
    let (log, next) := advance table state
    let (tail, residual) := runPrefix table fuel next
    (log ++ tail, residual)

def Compiled.start {source : Source.Module} (compiled : Compiled source)
    (globals : Core.Module.Globals := .empty) : State compiled.checked.tree.scope :=
  .ready (seed globals) compiled.instructions

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run
