module

public import Silmaril.Languages.Python.Compile.Closure.Thms

/-! # Source closure bodies awaiting code linking

The fixed positional profile lowers nested declarations, name reads and
writes, integer addition, integer multiplication and calls. A child declaration retains its
analyzed path, distinct parameter destinations and ordered capture
operands so a code linker can choose the numeric key.
-/

namespace Silmaril.Languages.Python.Compile.Closure.Body

open Source (BlockPath Name Scope ScopeTree)
open Core.Closure (CaptureSlot Parameters Slot TupleItem)

@[expose] public section

inductive GlobalRead (scope : Scope) (name : Name) : Prop where
  | implicit (access : scope.access name = some .implicitGlobal)
  | declared (access : scope.access name = some .declaredGlobal)

inductive Expr (layout : Core.Closure.Layout) where
  /-- Synthesized at the end of an ordinary function body. -/
  | none
  | integer (value : Int)
  /-- A literal Boolean test in a message-free body assertion. -/
  | boolean (value : Bool)
  | read (slot : Slot layout)
  | globalName (name : Name)
  /-- Equality against an integer literal in a message-free assertion. -/
  | eqInt (left : Expr layout) (right : Int)
  | add (left right : Expr layout)
  | mul (left right : Expr layout)
  | tuple (items : List (TupleItem layout))
  | call (callee : Expr layout) (arguments : List (Expr layout))
  deriving Repr

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleShape
  | bodyShape
  | unsupportedGenerator (path : BlockPath)
  | expressionShape
  | argumentProfile
  | unresolvedName (name : Name)
  | parameterProfile
  | parameterLayout (path : BlockPath)
  | scopeTree (path : BlockPath)
  | captureLayout (path : BlockPath)
  deriving Repr

inductive TupleItemTranslation (scope : Scope) : Source.Expr → TupleItem (frameLayout scope) → Prop where
  | integer (value : Int) : TupleItemTranslation scope (.integer value) (.literal (.int value))
  | boolean (value : Bool) : TupleItemTranslation scope (.boolean value) (.literal (.bool value))
  | none_ : TupleItemTranslation scope .none_ (.literal .none)
  | read {name slot} (translated : SlotTranslation scope name slot) :
      TupleItemTranslation scope (.name name) (.read slot)
  | global {name} (access : GlobalRead scope name) :
      TupleItemTranslation scope (.name name) (.global name)

inductive TupleItemsTranslation (scope : Scope) :
    List Source.Expr → List (TupleItem (frameLayout scope)) → Prop where
  | nil : TupleItemsTranslation scope [] []
  | cons {item items operand operands}
      (head : TupleItemTranslation scope item operand) (tail : TupleItemsTranslation scope items operands) :
      TupleItemsTranslation scope (item :: items) (operand :: operands)

mutual
  inductive ExprTranslation (scope : Scope) : Source.Expr → Expr (frameLayout scope) → Prop where
    | integer (value : Int) : ExprTranslation scope (.integer value) (.integer value)
    | read {name : Name} {slot : Slot (frameLayout scope)}
        (translated : SlotTranslation scope name slot) : ExprTranslation scope (.name name) (.read slot)
    | globalName {name : Name} (access : GlobalRead scope name) :
        ExprTranslation scope (.name name) (.globalName name)
    | add {left right lhs rhs} (leftTranslation : ExprTranslation scope left lhs)
        (rightTranslation : ExprTranslation scope right rhs) :
        ExprTranslation scope (.binary .add left right) (.add lhs rhs)
    | tuple {items operands} (checked : TupleItemsTranslation scope items operands) :
        ExprTranslation scope (.tuple items) (.tuple operands)
    | mul {left right lhs rhs} (leftTranslation : ExprTranslation scope left lhs)
        (rightTranslation : ExprTranslation scope right rhs) :
        ExprTranslation scope (.binary .mul left right) (.mul lhs rhs)
    | call {callee arguments targetCallee targetArguments}
        (function : ExprTranslation scope callee targetCallee)
        (positional : ArgumentsTranslation scope arguments targetArguments) :
        ExprTranslation scope (.call callee arguments) (.call targetCallee targetArguments)
    | callWith {callee arguments targetCallee targetArguments}
        (function : ExprTranslation scope callee targetCallee)
        (positional : TaggedArgumentsTranslation scope arguments targetArguments) :
        ExprTranslation scope (.callWith callee arguments) (.call targetCallee targetArguments)

  inductive ArgumentsTranslation (scope : Scope) :
      List Source.Expr → List (Expr (frameLayout scope)) → Prop where
    | nil : ArgumentsTranslation scope [] []
    | cons {source sources target targets} (first : ExprTranslation scope source target)
        (rest : ArgumentsTranslation scope sources targets) :
        ArgumentsTranslation scope (source :: sources) (target :: targets)

  inductive TaggedArgumentsTranslation (scope : Scope) :
      List (Source.ArgumentKind × Source.Expr) → List (Expr (frameLayout scope)) → Prop where
    | nil : TaggedArgumentsTranslation scope [] []
    | cons {source sources target targets} (first : ExprTranslation scope source target)
        (rest : TaggedArgumentsTranslation scope sources targets) :
        TaggedArgumentsTranslation scope ((.positional, source) :: sources) (target :: targets)
end

def lowerSlot (scope : Scope) (name : Name) :
    Except Error {slot // SlotTranslation scope name slot} := do
  let some result := slot? scope name | throw (.unresolvedName name)
  return result

def lowerNameRead (scope : Scope) (allowGlobals : Bool) (name : Name) :
    Except Error {operand // TupleItemTranslation scope (.name name) operand} :=
  if implicit : allowGlobals = true ∧ scope.access name = some .implicitGlobal then
    .ok ⟨.global name, .global (.implicit implicit.2)⟩
  else if declared : allowGlobals = true ∧ scope.access name = some .declaredGlobal then
    .ok ⟨.global name, .global (.declared declared.2)⟩
  else (lowerSlot scope name).map fun slot => ⟨.read slot.val, .read slot.property⟩

mutual
  def lowerExprWith (scope : Scope) (allowGlobals : Bool) : (source : Source.Expr) →
      Except Error {target // ExprTranslation scope source target}
    | .integer value => .ok ⟨.integer value, .integer value⟩
    | .name name => do
      let read ← lowerNameRead scope allowGlobals name
      match read with
      | ⟨.global global, evidence⟩ =>
        return ⟨.globalName global, by cases evidence with | global access => exact .globalName access⟩
      | ⟨.read slot, evidence⟩ =>
        return ⟨.read slot, by cases evidence with | read translated => exact .read translated⟩
      | ⟨.literal _, evidence⟩ => nomatch evidence
    | .binary .add left right => do
      let lhs ← lowerExprWith scope allowGlobals left
      let rhs ← lowerExprWith scope allowGlobals right
      return ⟨.add lhs.val rhs.val, .add lhs.property rhs.property⟩
    | .binary .mul left right => do
      let lhs ← lowerExprWith scope allowGlobals left
      let rhs ← lowerExprWith scope allowGlobals right
      return ⟨.mul lhs.val rhs.val, .mul lhs.property rhs.property⟩
    | .call callee arguments => do
      let function ← lowerExprWith scope allowGlobals callee
      let positional ← lowerArgumentsWith scope allowGlobals arguments
      return ⟨.call function.val positional.val, .call function.property positional.property⟩
    | .callWith callee arguments => do
      let function ← lowerExprWith scope allowGlobals callee
      let positional ← lowerTaggedArgumentsWith scope allowGlobals arguments
      return ⟨.call function.val positional.val, .callWith function.property positional.property⟩
    | _ => .error .expressionShape
  termination_by source => sizeOf source

  def lowerArgumentsWith (scope : Scope) (allowGlobals : Bool) : (sources : List Source.Expr) →
      Except Error {targets // ArgumentsTranslation scope sources targets}
    | [] => .ok ⟨[], .nil⟩
    | source :: rest => do
      let first ← lowerExprWith scope allowGlobals source
      let tail ← lowerArgumentsWith scope allowGlobals rest
      return ⟨first.val :: tail.val, .cons first.property tail.property⟩
  termination_by sources => sizeOf sources

  def lowerTaggedArgumentsWith (scope : Scope) (allowGlobals : Bool) : (sources : List (Source.ArgumentKind × Source.Expr)) →
      Except Error {targets // TaggedArgumentsTranslation scope sources targets}
    | [] => .ok ⟨[], .nil⟩
    | (.positional, source) :: rest => do
      let first ← lowerExprWith scope allowGlobals source
      let tail ← lowerTaggedArgumentsWith scope allowGlobals rest
      return ⟨first.val :: tail.val, .cons first.property tail.property⟩
    | _ => .error .argumentProfile
  termination_by sources => sizeOf sources
end

def lowerTupleItem (scope : Scope) (allowGlobals : Bool) : (item : Source.Expr) →
    Except Error {operand // TupleItemTranslation scope item operand}
  | .integer value => .ok ⟨.literal (.int value), .integer value⟩
  | .boolean value => .ok ⟨.literal (.bool value), .boolean value⟩
  | .none_ => .ok ⟨.literal .none, .none_⟩
  | .name name => lowerNameRead scope allowGlobals name
  | _ => .error .expressionShape

def lowerTupleItems (scope : Scope) (allowGlobals : Bool) : (items : List Source.Expr) →
    Except Error {operands // TupleItemsTranslation scope items operands}
  | [] => .ok ⟨[], .nil⟩
  | head :: tail => do
    let first ← lowerTupleItem scope allowGlobals head
    let remaining ← lowerTupleItems scope allowGlobals tail
    return ⟨first.val :: remaining.val, .cons first.property remaining.property⟩

/-- Tuple syntax is admitted at return sites. The ordinary operand checker
continues to govern assignments and call arguments. -/
def lowerReturnExpr (scope : Scope) (allowGlobals : Bool) : (source : Source.Expr) →
    Except Error {target // ExprTranslation scope source target}
  | .tuple items => (lowerTupleItems scope allowGlobals items).map fun checked =>
      ⟨.tuple checked.val, .tuple checked.property⟩
  | source => lowerExprWith scope allowGlobals source

def lowerExpr (scope : Scope) := lowerExprWith scope false

def lowerArguments (scope : Scope) := lowerArgumentsWith scope false

def lowerTaggedArguments (scope : Scope) := lowerTaggedArgumentsWith scope false

/-- Path references are resolved by a later code linker. Both the call
arguments and the capture operands retain their source order. -/
inductive Code : Core.Closure.Layout → Type where
  | ret {layout} (value : Expr layout) : Code layout
  | assert {layout} (test : Expr layout) (next : Code layout) : Code layout
  | assertFreeVars {layout} (receiver : Expr layout) (needle : List UInt32) (expected : Bool)
      (next : Code layout) : Code layout
  | assertCellVars {layout} (receiver : Expr layout) (needle : List UInt32) (next : Code layout) : Code layout
  | assertCodeNames {layout} (receiver : Expr layout) (needle : List UInt32) (next : Code layout) : Code layout
  | discardCall {layout} (callee : Expr layout) (next : Code layout) : Code layout
  | assign {layout} (destination : Slot layout) (value : Expr layout) (next : Code layout) : Code layout
  | closure {layout} (destination : Slot layout) (path : BlockPath) (childLayout : Core.Closure.Layout)
      (parameters : Parameters childLayout) (captures : Fin childLayout.captures → CaptureSlot layout)
      (child : Code childLayout) (next : Code layout) : Code layout

  /-- Return the child closure itself, or the result of invoking it with the supplied operands. -/
  | returnClosure {layout} (path : BlockPath) (childLayout : Core.Closure.Layout)
      (parameters : Parameters childLayout) (captures : Fin childLayout.captures → CaptureSlot layout)
      (child : Code childLayout) (arguments : Option (List (Expr layout))) : Code layout

/-- Child code paths in lexical preorder. -/
def Code.childPaths {layout : Core.Closure.Layout} : Code layout → List BlockPath
  | .ret _ => []
  | .assign _ _ next | .assert _ next | .assertFreeVars _ _ _ next
  | .assertCellVars _ _ next | .assertCodeNames _ _ next | .discardCall _ next => next.childPaths
  | .closure _ path _ _ _ child next => path :: (child.childPaths ++ next.childPaths)
  | .returnClosure path _ _ _ child _ => path :: child.childPaths

def fixed (parameter : Source.Parameter) : Bool :=
  parameter.defaultValue.isNone && parameter.annotation.isNone &&
    match parameter.kind with
    | .positionalOnly | .positionalOrKeyword => true
    | _ => false

def checkParameters (scope : Scope) (declaration : List Source.Parameter) :
    Except Error {target : Parameters (frameLayout scope) // declaration.all fixed = true ∧
      target.slots.map (parameterName scope) = declaration.map Source.Parameter.name} := do
  if profile : declaration.all fixed = true then
    if names : scope.context.parameters = declaration.map Source.Parameter.name then
      let some checked := Source.Closure.Frame.parameterLayout? scope
        | throw (.parameterLayout scope.context.path)
      return ⟨parameters checked, profile, (parameters_order checked).trans names⟩
    else throw (.scopeTree scope.context.path)
  else throw .parameterProfile

inductive Assignment : Source.Stmt → Name → Source.Expr → Prop where
  | simple (name : Name) (value : Source.Expr) : Assignment (.assign name value) name value
  | singleTarget (name : Name) (value : Source.Expr) : Assignment (.assignTargets [.name name] value) name value

def assignment? : (source : Source.Stmt) →
    Option {binding : Name × Source.Expr // Assignment source binding.1 binding.2}
  | .assign name value => some ⟨(name, value), .simple name value⟩
  | .assignTargets [.name name] value => some ⟨(name, value), .singleTarget name value⟩
  | _ => none

inductive ZeroArgumentNameCall : Source.Expr → Name → Prop where
  | plain (name : Name) : ZeroArgumentNameCall (.call (.name name) []) name
  | tagged (name : Name) : ZeroArgumentNameCall (.callWith (.name name) []) name

def zeroArgumentNameCall? : (source : Source.Expr) →
    Option {name // ZeroArgumentNameCall source name}
  | .call (.name name) [] => some ⟨name, .plain name⟩
  | .callWith (.name name) [] => some ⟨name, .tagged name⟩
  | _ => none

inductive FreeVarsTest : Source.Expr → Name → List UInt32 → Bool → Prop where
  | contains (function : Name) (name : List UInt32) :
      FreeVarsTest
        (.comparison (.text name) [(.in_, .attribute (.attribute (.name function) "__code__") "co_freevars")])
        function name true
  | excludes (function : Name) (name : List UInt32) :
      FreeVarsTest
        (.comparison (.text name) [(.notIn, .attribute (.attribute (.name function) "__code__") "co_freevars")])
        function name false

def freeVarsTest? : (source : Source.Expr) →
    Option {test : Name × List UInt32 × Bool // FreeVarsTest source test.1 test.2.1 test.2.2}
  | .comparison (.text name) [(.in_, .attribute (.attribute (.name function) "__code__") "co_freevars")] =>
    some ⟨(function, name, true), .contains function name⟩
  | .comparison (.text name) [(.notIn, .attribute (.attribute (.name function) "__code__") "co_freevars")] =>
    some ⟨(function, name, false), .excludes function name⟩
  | _ => none

inductive CellVarsTest : Source.Expr → Name → List UInt32 → Prop where
  | excludes (function : Name) (name : List UInt32) :
      CellVarsTest
        (.comparison (.text name) [(.notIn, .attribute (.attribute (.name function) "__code__") "co_cellvars")])
        function name

def cellVarsTest? : (source : Source.Expr) →
    Option {test : Name × List UInt32 // CellVarsTest source test.1 test.2}
  | .comparison (.text name) [(.notIn, .attribute (.attribute (.name function) "__code__") "co_cellvars")] =>
    some ⟨(function, name), .excludes function name⟩
  | _ => none

inductive CodeNamesTest : Source.Expr → Name → List UInt32 → Prop where
  | contains (function : Name) (name : List UInt32) :
      CodeNamesTest
        (.comparison (.text name) [(.in_, .attribute (.attribute (.name function) "__code__") "co_names")])
        function name

def codeNamesTest? : (source : Source.Expr) →
    Option {test : Name × List UInt32 // CodeNamesTest source test.1 test.2}
  | .comparison (.text name) [(.in_, .attribute (.attribute (.name function) "__code__") "co_names")] =>
    some ⟨(function, name), .contains function name⟩
  | _ => none

/-- A terminal lambda either returns its descriptor or is called immediately
with positional operands evaluated in the surrounding frame. -/
inductive TerminalLambda (scope : Scope) :
    Source.Expr → List Source.Parameter → Source.Expr → Option (List (Expr (frameLayout scope))) → Prop where
  | value (declaration : List Source.Parameter) (body : Source.Expr) :
      TerminalLambda scope (.lambda declaration body) declaration body none
  | call {declaration body arguments operands} (positional : ArgumentsTranslation scope arguments operands) :
      TerminalLambda scope (.call (.lambda declaration body) arguments) declaration body (some operands)
  | callWith {declaration body arguments operands}
      (positional : TaggedArgumentsTranslation scope arguments operands) :
      TerminalLambda scope (.callWith (.lambda declaration body) arguments) declaration body (some operands)

private theorem TerminalLambda.body_lt {scope : Scope} {source declaration body arguments}
    (shape : TerminalLambda scope source declaration body arguments) : sizeOf body < sizeOf source := by
  cases shape <;> simp <;> omega

private def terminalLambda? (scope : Scope) (allowGlobals : Bool) : (source : Source.Expr) →
    Option (Except Error {result : List Source.Parameter × Source.Expr × Option (List (Expr (frameLayout scope))) //
      TerminalLambda scope source result.1 result.2.1 result.2.2})
  | .lambda declaration body => some (.ok ⟨(declaration, body, none), .value declaration body⟩)
  | .call (.lambda declaration body) arguments => some do
    let positional ← lowerArgumentsWith scope allowGlobals arguments
    return ⟨(declaration, body, some positional.val), .call positional.property⟩
  | .callWith (.lambda declaration body) arguments => some do
    let positional ← lowerTaggedArgumentsWith scope allowGlobals arguments
    return ⟨(declaration, body, some positional.val), .callWith positional.property⟩
  | _ => none

inductive Translation : (tree : ScopeTree) → Nat → List Source.Stmt →
    Code (frameLayout tree.scope) → Prop where
  | ret {tree index source target} (ordinary : tree.scope.context.containsYield = false)
      (complete : index = tree.children.length)
      (value : ExprTranslation tree.scope source target) :
      Translation tree index [.return_ (some source)] (.ret target)
  | fallthrough {tree index} (ordinary : tree.scope.context.containsYield = false)
      (complete : index = tree.children.length) :
      Translation tree index [] (.ret .none)
  | assign {tree index statement name source rest slot target next}
      (assignment : Assignment statement name source) (destination : SlotTranslation tree.scope name slot)
      (value : ExprTranslation tree.scope source target) (tail : Translation tree index rest next) :
      Translation tree index (statement :: rest) (.assign slot target next)
  | assert {tree index source target rest next}
      (test : ExprTranslation tree.scope source target) (tail : Translation tree index rest next) :
      Translation tree index (.assert_ source none :: rest) (.assert target next)
  | assertBoolean {tree index value rest next} (tail : Translation tree index rest next) :
      Translation tree index (.assert_ (.boolean value) none :: rest) (.assert (.boolean value) next)
  | assertEqInt {tree index name left right rest next}
      (read : ExprTranslation tree.scope (.name name) left)
      (tail : Translation tree index rest next) :
      Translation tree index (.assert_ (.comparison (.name name) [(.eq, .integer right)]) none :: rest)
        (.assert (.eqInt left right) next)
  | assertFreeVars {tree index source name function member expected rest next}
      (shape : FreeVarsTest source name member expected)
      (read : ExprTranslation tree.scope (.name name) function)
      (tail : Translation tree index rest next) :
      Translation tree index (.assert_ source none :: rest)
        (.assertFreeVars function member expected next)
  | assertCellVars {tree index source name function member rest next}
      (shape : CellVarsTest source name member)
      (read : ExprTranslation tree.scope (.name name) function)
      (tail : Translation tree index rest next) :
      Translation tree index (.assert_ source none :: rest) (.assertCellVars function member next)
  | assertCodeNames {tree index source name function member rest next}
      (shape : CodeNamesTest source name member)
      (read : ExprTranslation tree.scope (.name name) function)
      (tail : Translation tree index rest next) :
      Translation tree index (.assert_ source none :: rest) (.assertCodeNames function member next)
  | discardCall {tree index source name callee rest next}
      (shape : ZeroArgumentNameCall source name)
      (read : ExprTranslation tree.scope (.name name) callee)
      (tail : Translation tree index rest next) :
      Translation tree index (.expression source :: rest) (.discardCall callee next)
  | pass {tree index rest next} (tail : Translation tree index rest next) :
      Translation tree index (.pass :: rest) next
  | nonlocal {tree index names rest next} (tail : Translation tree index rest next) :
      Translation tree index (.nonlocalDecl names :: rest) next
  | global {tree index names rest next} (tail : Translation tree index rest next) :
      Translation tree index (.globalDecl names :: rest) next
  | closure {tree index name declaration body rest slot child parameters code next}
      (found : tree.children[index]? = some child)
      (path : child.scope.context.path = tree.scope.context.path ++ [index])
      (kind : child.scope.context.kind = .function)
      (destination : SlotTranslation tree.scope name slot)
      (fixedPosition : declaration.all fixed = true)
      (parameterOrder : parameters.slots.map (parameterName child.scope) = declaration.map Source.Parameter.name)
      (captures : Source.Closure.Layout tree.scope child.scope.captures)
      (translated : Translation child 0 body code) (tail : Translation tree (index + 1) rest next) :
      Translation tree index (.functionDef name declaration body [] none :: rest)
        (.closure slot (tree.scope.context.path ++ [index]) (frameLayout child.scope) parameters
          (captureOperands captures) code next)

  | returnLambda {tree index source declaration body child parameters code arguments}
      (shape : TerminalLambda tree.scope source declaration body arguments)
      (ordinary : tree.scope.context.containsYield = false) (complete : index + 1 = tree.children.length)
      (found : tree.children[index]? = some child)
      (path : child.scope.context.path = tree.scope.context.path ++ [index])
      (kind : child.scope.context.kind = .function)
      (fixedPosition : declaration.all fixed = true)
      (parameterOrder : parameters.slots.map (parameterName child.scope) = declaration.map Source.Parameter.name)
      (captures : Source.Closure.Layout tree.scope child.scope.captures)
      (translated : Translation child 0 [.return_ (some body)] code) :
      Translation tree index [.return_ (some source)]
        (.returnClosure (tree.scope.context.path ++ [index]) (frameLayout child.scope)
          parameters (captureOperands captures) code arguments)

private def lowerOrdinaryBody (tree : ScopeTree) (allowGlobals : Bool)
    (ordinary : tree.scope.context.containsYield = false) (childIndex : Nat) :
    (body : List Source.Stmt) →
    Except Error {target // Translation tree childIndex body target}
  | [.return_ (some value)] => do
    if let some terminal := terminalLambda? tree.scope allowGlobals value then
      let ⟨(declaration, body, arguments), shape⟩ ← terminal
      unless declaration.all fixed do throw .parameterProfile
      let path := tree.scope.context.path ++ [childIndex]
      match found : tree.children[childIndex]? with
      | none => throw (.scopeTree path)
      | some child =>
        if scopeMatches : child.scope.context.path = path ∧ child.scope.context.kind = .function then
          if complete : childIndex + 1 = tree.children.length then
            let childOrdinary ← if clear : child.scope.context.containsYield = false then
              pure (PLift.up clear)
            else throw (.unsupportedGenerator path)
            let slots ← checkParameters child.scope declaration
            let some captures := Source.Closure.layout? tree.scope child.scope.captures
              | throw (.captureLayout path)
            let code ← lowerOrdinaryBody child allowGlobals childOrdinary.down 0 [.return_ (some body)]
            return ⟨.returnClosure path (frameLayout child.scope) slots.val (captureOperands captures) code.val arguments,
              .returnLambda shape ordinary complete found scopeMatches.1 scopeMatches.2
                slots.property.1 slots.property.2 captures code.property⟩
          else throw (.scopeTree path)
        else throw (.scopeTree path)
    else if complete : childIndex = tree.children.length then
      let target ← lowerReturnExpr tree.scope allowGlobals value
      return ⟨.ret target.val, .ret ordinary complete target.property⟩
    else throw (.scopeTree tree.scope.context.path)
  | .assert_ (.boolean value) none :: rest => do
    let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨.assert (.boolean value) tail.val, .assertBoolean tail.property⟩
  | .assert_ (.comparison (.name name) [(.eq, .integer right)]) none :: rest => do
    let left ← lowerExprWith tree.scope allowGlobals (.name name)
    let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨.assert (.eqInt left.val right) tail.val, .assertEqInt left.property tail.property⟩
  | .assert_ test none :: rest => do
    if let some ⟨(function, name, expected), shape⟩ := freeVarsTest? test then
      let read ← lowerExprWith tree.scope allowGlobals (.name function)
      let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
      return ⟨.assertFreeVars read.val name expected tail.val,
        .assertFreeVars shape read.property tail.property⟩
    else if let some ⟨(function, name), shape⟩ := cellVarsTest? test then
      let read ← lowerExprWith tree.scope allowGlobals (.name function)
      let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
      return ⟨.assertCellVars read.val name tail.val, .assertCellVars shape read.property tail.property⟩
    else if let some ⟨(function, name), shape⟩ := codeNamesTest? test then
      let read ← lowerExprWith tree.scope allowGlobals (.name function)
      let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
      return ⟨.assertCodeNames read.val name tail.val, .assertCodeNames shape read.property tail.property⟩
    else
      let target ← lowerExprWith tree.scope allowGlobals test
      let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
      return ⟨.assert target.val tail.val, .assert target.property tail.property⟩
  | .expression source :: rest => do
    let some call := zeroArgumentNameCall? source | throw .bodyShape
    let callee ← lowerExprWith tree.scope allowGlobals (.name call.val)
    let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨.discardCall callee.val tail.val, .discardCall call.property callee.property tail.property⟩
  | .pass :: rest => do
    let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨tail.val, .pass tail.property⟩
  | .nonlocalDecl _ :: rest => do
    let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨tail.val, .nonlocal tail.property⟩
  | .globalDecl _ :: rest => do
    unless allowGlobals do throw .bodyShape
    let tail ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨tail.val, .global tail.property⟩
  | .functionDef name declaration body [] none :: rest => do
    let path := tree.scope.context.path ++ [childIndex]
    match found : tree.children[childIndex]? with
    | none => throw (.scopeTree path)
    | some child =>
      if scopeMatches : child.scope.context.path = path ∧ child.scope.context.kind = .function then
        let childOrdinary ← if clear : child.scope.context.containsYield = false then
          pure (PLift.up clear)
        else throw (.unsupportedGenerator path)
        let destination ← lowerSlot tree.scope name
        let parameterSlots ← checkParameters child.scope declaration
        let some captures := Source.Closure.layout? tree.scope child.scope.captures | throw (.captureLayout path)
        let code ← lowerOrdinaryBody child allowGlobals childOrdinary.down 0 body
        let next ← lowerOrdinaryBody tree allowGlobals ordinary (childIndex + 1) rest
        return ⟨.closure destination.val path (frameLayout child.scope) parameterSlots.val
          (captureOperands captures) code.val next.val,
          .closure found scopeMatches.1 scopeMatches.2 destination.property parameterSlots.property.1
            parameterSlots.property.2 captures code.property next.property⟩
      else throw (.scopeTree path)
  | statement :: rest => do
    let some ⟨(name, value), assignment⟩ := assignment? statement | throw .bodyShape
    let destination ← lowerSlot tree.scope name
    let target ← lowerExprWith tree.scope allowGlobals value
    let next ← lowerOrdinaryBody tree allowGlobals ordinary childIndex rest
    return ⟨.assign destination.val target.val next.val,
      .assign assignment destination.property target.property next.property⟩
  | [] =>
    if complete : childIndex = tree.children.length then
      .ok ⟨.ret .none, .fallthrough ordinary complete⟩
    else .error (.scopeTree tree.scope.context.path)
termination_by body => sizeOf body
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have smaller := shape.body_lt; omega

end

public def lowerBodyWith (tree : ScopeTree) (allowGlobals : Bool) (childIndex : Nat)
    (body : List Source.Stmt) : Except Error {target // Translation tree childIndex body target} :=
  if ordinary : tree.scope.context.containsYield = false then
    lowerOrdinaryBody tree allowGlobals ordinary childIndex body
  else .error (.unsupportedGenerator tree.scope.context.path)

@[expose] public section

def lowerBody (tree : ScopeTree) := lowerBodyWith tree false

structure Compiled (source : Source.Module) where
  name : Name
  declaration : List Source.Parameter
  body : List Source.Stmt
  shape : source.body = [.functionDef name declaration body [] none]
  tree : ScopeTree
  moduleTree : ScopeTree
  analyzed : Source.analyze source = .ok moduleTree
  located : moduleTree.children = [tree]
  parameters : Parameters (frameLayout tree.scope)
  fixedPosition : declaration.all fixed = true
  parameterOrder : parameters.slots.map (parameterName tree.scope) = declaration.map Source.Parameter.name
  code : Code (frameLayout tree.scope)
  translated : Translation tree 0 body code

def Compiled.paths {source : Source.Module} (compiled : Compiled source) : List BlockPath :=
  compiled.tree.scope.context.path :: compiled.code.childPaths

def compile (source : Source.Module) : Except Error (Compiled source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    match shape : source.body, located : tree.children with
    | [.functionDef name declaration body [] none], [entry] => do
      let parameters ← checkParameters entry.scope declaration
      let code ← lowerBody entry 0 body
      return ⟨name, declaration, body, shape, entry, tree, analyzed, located, parameters.val,
        parameters.property.1, parameters.property.2, code.val, code.property⟩
    | _, _ => .error .moduleShape

end

end Silmaril.Languages.Python.Compile.Closure.Body
