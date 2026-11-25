module

public import Silmaril.Languages.Python.Source.Syntax.Defs

/-! # Lexical scope of the Python module, function and class fragment

Collect declarations and binding occurrences in source order. Resolve names
using whole-block information, including assignments later in the block.
Child blocks retain both their directly used free names and any captures
they forward for descendants. Paths index child blocks in source order.
-/

namespace Silmaril.Languages.Python.Source

@[expose] public section

abbrev BlockPath := List Nat

inductive BlockKind where
  | module_
  | function
  | class_
  deriving BEq, DecidableEq, Repr

structure BlockContext where
  path : BlockPath
  kind : BlockKind
  parameters : List Name := []
  assigned : List Name := []
  read : List Name := []
  globals : List Name := []
  nonlocals : List Name := []
  deriving Repr

/-- A module, or an explicit global declaration in a function, ends the search. -/
def BlockContext.lookupBarrier (block : BlockContext) (name : Name) : Bool :=
  match block.kind with
  | .module_ => true
  | .function => block.globals.contains name
  | .class_ => false

/-- Closure binders of an enclosing block, including the synthetic class cell. -/
def BlockContext.binds (block : BlockContext) (name : Name) : Bool :=
  match block.kind with
  | .module_ => false
  | .function =>
    !block.globals.contains name && !block.nonlocals.contains name &&
      (block.parameters.contains name || block.assigned.contains name)
  | .class_ => name == "__class__"

/-- Search ancestors in order from the immediately enclosing block. -/
def enclosingBinding (name : Name) : List BlockContext → Option BlockPath
  | [] => none
  | block :: outer =>
    if block.lookupBarrier name then none
    else if block.binds name then some block.path
    else enclosingBinding name outer

/-- Independent characterization of a visible enclosing binder. -/
inductive EnclosingBinding (name : Name) : List BlockContext → BlockPath → Prop where
  | nearest {block outer} (visible : block.lookupBarrier name = false)
      (binds : block.binds name = true) :
      EnclosingBinding name (block :: outer) block.path
  | outside {block outer path} (visible : block.lookupBarrier name = false)
      (skips : block.binds name = false) (found : EnclosingBinding name outer path) :
      EnclosingBinding name (block :: outer) path

inductive Access where
  | moduleName
  | local
  | className
  | declaredGlobal
  | implicitGlobal
  | free (origin : BlockPath)
  | classFree (origin : BlockPath)
  deriving BEq, DecidableEq, Repr

structure Capture where
  name : Name
  origin : BlockPath
  deriving BEq, DecidableEq, Repr

inductive NameUse where
  | read | implicitRead | assign | delete | parameter | definition | import_
  | exceptionTarget | globalDeclaration | nonlocalDeclaration
  deriving BEq, DecidableEq, Repr

structure Occurrence where
  name : Name
  use : NameUse
  deriving BEq, DecidableEq, Repr

structure ResolvedOccurrence (accesses : List (Name × Access)) where
  occurrence : Occurrence
  access : Access
  lookup_eq : accesses.lookup occurrence.name = some access
  deriving Repr

structure Scope where
  context : BlockContext
  accesses : List (Name × Access)
  cells : List Name
  captures : List Capture
  /-- Each entry's index is its ordinal in this lexical block's traversal. -/
  occurrences : List (ResolvedOccurrence accesses)
  deriving Repr

def Scope.access (scope : Scope) (name : Name) : Option Access :=
  scope.accesses.lookup name

inductive ScopeTree where
  | block (scope : Scope) (children : List ScopeTree)
  deriving Repr

def ScopeTree.scope : ScopeTree → Scope
  | .block scope _ => scope

def ScopeTree.children : ScopeTree → List ScopeTree
  | .block _ children => children

def ScopeTree.atPath (tree : ScopeTree) : BlockPath → Option Scope
  | [] => some tree.scope
  | child :: rest => (tree.children[child]?).bind (fun nested => nested.atPath rest)

inductive Directive where
  | global_
  | nonlocal_
  deriving BEq, DecidableEq, Repr

inductive ScopeError where
  | duplicateParameter (name : Name)
  | lambdaParameterAnnotation (name : Name)
  | parameterDirective (name : Name) (directive : Directive)
  | conflictingDirectives (name : Name)
  | readBeforeDirective (name : Name) (directive : Directive)
  | boundBeforeDirective (name : Name) (directive : Directive)
  | nonlocalInModule (name : Name)
  | unboundNonlocal (name : Name)
  | starImport
  | unsupportedExpression (form : UnsupportedExpr)
  | missingOccurrenceBinding (name : Name)
  deriving BEq, DecidableEq, Repr

inductive AnnotationMode where
  | eager
  | deferred
  deriving BEq, DecidableEq, Repr

/-- The permissive mode treats an unresolved nonlocal as a global access. -/
inductive NonlocalPolicy where
  | reject
  | globalFallback
  deriving BEq, DecidableEq, Repr

structure Diagnostic where
  path : BlockPath
  error : ScopeError
  deriving BEq, DecidableEq, Repr

end

private inductive CollectedTree where
  | block (context : BlockContext) (occurrences : List Occurrence) (children : List CollectedTree)

private def recordName (names : List Name) (name : Name) : List Name :=
  if names.contains name then names else name :: names

private def collectDirective (block : BlockContext) (directive : Directive)
    (name : Name) : Except Diagnostic BlockContext := do
  if block.parameters.contains name then
    throw ⟨block.path, .parameterDirective name directive⟩
  let isGlobal := directive == .global_
  let conflicts := if isGlobal then block.nonlocals else block.globals
  if conflicts.contains name then
    throw ⟨block.path, .conflictingDirectives name⟩
  if block.read.contains name then
    throw ⟨block.path, .readBeforeDirective name directive⟩
  if block.assigned.contains name then
    throw ⟨block.path, .boundBeforeDirective name directive⟩
  if isGlobal then
    return { block with globals := recordName block.globals name }
  if block.kind == .module_ then
    throw ⟨block.path, .nonlocalInModule name⟩
  return { block with nonlocals := recordName block.nonlocals name }

private structure Collecting where
  context : BlockContext
  annotationMode : AnnotationMode
  childrenRev : List CollectedTree := []
  occurrencesRev : List Occurrence := []

private def Collecting.note (block : Collecting) (name : Name) (use : NameUse) : Collecting :=
  { block with occurrencesRev := ⟨name, use⟩ :: block.occurrencesRev }

private def Collecting.readName (block : Collecting) (name : Name) : Collecting :=
  let block := block.note name .read
  let read := recordName block.context.read name
  if block.context.kind == .function && name == "super" then
    { block.note "__class__" .implicitRead with
      context := { block.context with read := recordName read "__class__" } }
  else
    { block with context := { block.context with read } }

private def Collecting.bindName (block : Collecting) (name : Name) (use : NameUse) : Collecting :=
  { block.note name use with
    context := { block.context with assigned := recordName block.context.assigned name } }

private def Collecting.childPath (block : Collecting) : BlockPath :=
  block.context.path ++ [block.childrenRev.length]

private def Collecting.startChild (block : Collecting) (context : BlockContext) : Collecting :=
  { context, annotationMode := block.annotationMode
    occurrencesRev := context.parameters.reverse.map (fun name => ⟨name, .parameter⟩) }

private def Collecting.finish (block : Collecting) : CollectedTree :=
  .block block.context block.occurrencesRev.reverse block.childrenRev.reverse

private def Collecting.addChild (block child : Collecting) : Collecting :=
  { block with childrenRev := child.finish :: block.childrenRev }

private def functionContext (path : BlockPath)
    (parameters : List Parameter) : Except Diagnostic BlockContext := do
  let names ← parameters.foldlM (init := []) fun names parameter => do
    if names.contains parameter.name then
      throw ⟨path, .duplicateParameter parameter.name⟩
    return parameter.name :: names
  return { path, kind := .function, parameters := names.reverse }

private def Collecting.importName (block : Collecting) (name : ImportName) :
    Except Diagnostic Collecting :=
  if name.member == "*" then .error ⟨block.context.path, .starImport⟩
  else .ok (block.bindName (name.alias.getD name.member) .import_)

mutual
  private def collect (block : Collecting) : List Stmt → Except Diagnostic Collecting
    | [] => .ok block
    | stmt :: rest => do collect (← collectStmt block stmt) rest

  private def collectStmt (block : Collecting) : Stmt → Except Diagnostic Collecting
    | .assign target value => do return (← collectExpr block value).bindName target .assign
    | .assignTargets targets value => do collectTargets .assign (← collectExpr block value) targets
    | .delete target => .ok (block.bindName target .delete)
    | .deleteTargets targets => collectTargets .delete block targets
    | .expression value | .return_ (some value) => collectExpr block value
    | .pass | .break_ | .continue_ | .return_ none => .ok block
    | .raise_ exception cause => do collectOptional (← collectOptional block exception) cause
    | .assert_ condition message => do collectOptional (← collectExpr block condition) message
    | .globalDecl names => do
      let context ← names.foldlM (fun ctx name => collectDirective ctx .global_ name) block.context
      let block := names.foldl (fun acc name => acc.note name .globalDeclaration) block
      return { block with context }
    | .nonlocalDecl names => do
      let context ← names.foldlM (fun ctx name => collectDirective ctx .nonlocal_ name) block.context
      let block := names.foldl (fun acc name => acc.note name .nonlocalDeclaration) block
      return { block with context }
    | .if_ condition body otherwise | .while_ condition body otherwise => do
      collect (← collect (← collectExpr block condition) body) otherwise
    | .for_ target iterator body otherwise => do
      let outer ← collectTarget .assign (← collectExpr block iterator) target
      collect (← collect outer body) otherwise
    | .try_ body handlers otherwise cleanup => do
      let afterHandlers ← collectHandlers (← collect block body) handlers
      collect (← collect afterHandlers otherwise) cleanup
    | .importFrom _ _ names => names.foldlM Collecting.importName block
    | .functionDef name parameters body decorators returnAnnotation => do
      let outer ← collectDefaults block parameters
      let outer ← if block.annotationMode == .eager then do
        collectOptional (← collectAnnotations outer parameters) returnAnnotation
      else pure outer
      let outer ← collectExprs outer decorators
      let context ← functionContext outer.childPath parameters
      let nested ← collect (outer.startChild context) body
      return (outer.bindName name .definition).addChild nested
    | .classDef name bases body decorators keywords => do
      let outer ← collectExprs (← collectExprs block decorators) bases
      let outer ← collectClassKeywords outer keywords
      let nested ← collect (outer.startChild { path := outer.childPath, kind := .class_ }) body
      return (outer.bindName name .definition).addChild nested

  private def collectExpr (block : Collecting) : Expr → Except Diagnostic Collecting
    | .name name => .ok (block.readName name)
    | .list_ elements | .tuple elements | .booleanOp _ elements => collectExprs block elements
    | .dictionary entries => do collectDictValues (← collectDictKeys block entries) entries
    | .unary _ operand => collectExpr block operand
    | .binary _ left right => do collectExpr (← collectExpr block left) right
    | .conditional condition consequent alternate => do
      collectExpr (← collectExpr (← collectExpr block condition) consequent) alternate
    | .comparison left rest => do collectComparands (← collectExpr block left) rest
    | .call callee arguments => do collectExprs (← collectExpr block callee) arguments
    | .callWith callee arguments => do collectArguments (← collectExpr block callee) arguments
    | .starred value => collectExpr block value
    | .attribute receiver _ => collectExpr block receiver
    | .subscript receiver index => do collectExpr (← collectExpr block receiver) index
    | .slice receiver lower upper stride => do
      let block ← collectExpr block receiver
      collectOptional (← collectOptional (← collectOptional block lower) upper) stride
    | .yield_ value => collectOptional block value
    | .lambda parameters body => do
      let outer ← collectDefaults block parameters
      let context ← functionContext outer.childPath parameters
      if let some annotated := parameters.find? (·.annotation.isSome) then
        throw ⟨context.path, .lambdaParameterAnnotation annotated.name⟩
      let nested ← collectExpr (outer.startChild context) body
      return outer.addChild nested
    | .integer _ | .floatBits _ | .text _ | .boolean _ | .none_ | .ellipsis => .ok block
    | .unsupported form => .error ⟨block.context.path, .unsupportedExpression form⟩

  private def collectExprs (block : Collecting) : List Expr → Except Diagnostic Collecting
    | [] => .ok block
    | expr :: rest => do collectExprs (← collectExpr block expr) rest

  private def collectDictKeys (block : Collecting) :
      List (Option Expr × Expr) → Except Diagnostic Collecting
    | [] => .ok block
    | (key, _) :: rest => do collectDictKeys (← collectOptional block key) rest

  private def collectDictValues (block : Collecting) :
      List (Option Expr × Expr) → Except Diagnostic Collecting
    | [] => .ok block
    | (_, value) :: rest => do collectDictValues (← collectExpr block value) rest

  private def collectComparands (block : Collecting) :
      List (Comparison × Expr) → Except Diagnostic Collecting
    | [] => .ok block
    | (_, value) :: rest => do collectComparands (← collectExpr block value) rest

  private def collectArguments (block : Collecting) :
      List (ArgumentKind × Expr) → Except Diagnostic Collecting
    | [] => .ok block
    | (_, value) :: rest => do collectArguments (← collectExpr block value) rest

  private def collectClassKeywords (block : Collecting) :
      List (Option Name × Expr) → Except Diagnostic Collecting
    | [] => .ok block
    | (_, value) :: rest => do collectClassKeywords (← collectExpr block value) rest

  private def collectDefaults (block : Collecting) : List Parameter → Except Diagnostic Collecting
    | [] => .ok block
    | ⟨_, defaultValue, _, _⟩ :: rest => do
      collectDefaults (← collectOptional block defaultValue) rest

  private def collectAnnotations (block : Collecting) : List Parameter → Except Diagnostic Collecting
    | [] => .ok block
    | ⟨_, _, _, annotation⟩ :: rest => do
      collectAnnotations (← collectOptional block annotation) rest

  private def collectOptional (block : Collecting) : Option Expr → Except Diagnostic Collecting
    | none => .ok block
    | some expr => collectExpr block expr

  private def collectTarget (use : NameUse) (block : Collecting) : Target → Except Diagnostic Collecting
    | .name name => .ok (block.bindName name use)
    | .attribute receiver _ => collectExpr block receiver
    | .subscript receiver index => do collectExpr (← collectExpr block receiver) index
    | .tuple targets | .list_ targets => collectTargets use block targets

  private def collectTargets (use : NameUse) (block : Collecting) :
      List Target → Except Diagnostic Collecting
    | [] => .ok block
    | target :: rest => do collectTargets use (← collectTarget use block target) rest

  private def collectHandlers (block : Collecting) :
      List ExceptHandler → Except Diagnostic Collecting
    | [] => .ok block
    | ⟨condition, target, body⟩ :: rest => do
      let block ← collectOptional block condition
      let block := target.elim block (fun name => block.bindName name .exceptionTarget)
      collectHandlers (← collect block body) rest
end

private def BlockContext.mentionedNames (block : BlockContext) : List Name :=
  (block.parameters ++ block.assigned.reverse ++ block.read.reverse ++
    block.globals.reverse ++ block.nonlocals.reverse).eraseDups

private def resolveName (nonlocalPolicy : NonlocalPolicy) (block : BlockContext) (outer : List BlockContext)
    (name : Name) : Except Diagnostic (Name × Access) :=
  if block.globals.contains name then .ok (name, .declaredGlobal)
  else if block.kind == .module_ then .ok (name, .moduleName)
  else if block.kind == .function && block.binds name then .ok (name, .local)
  else if block.kind == .class_ && block.assigned.contains name && !block.nonlocals.contains name
    then .ok (name, .className)
  else match enclosingBinding name outer with
    | some path =>
      .ok (name, if block.kind == .class_ then .classFree path else .free path)
    | none =>
      if block.nonlocals.contains name then
        match nonlocalPolicy with
        | .reject => .error ⟨block.path, .unboundNonlocal name⟩
        | .globalFallback => .ok (name, .implicitGlobal)
      else if block.kind == .class_ then .ok (name, .className)
      else .ok (name, .implicitGlobal)

private def directCaptures (accesses : List (Name × Access)) : List Capture :=
  accesses.filterMap fun (name, access) => match access with
    | .free origin | .classFree origin => some ⟨name, origin⟩
    | _ => none

private def resolveOccurrence (context : BlockContext) (accesses : List (Name × Access))
    (occurrence : Occurrence) : Except Diagnostic (ResolvedOccurrence accesses) :=
  match lookup : accesses.lookup occurrence.name with
  | some access => .ok ⟨occurrence, access, lookup⟩
  | none => .error ⟨context.path, .missingOccurrenceBinding occurrence.name⟩

mutual
  private def resolve (nonlocalPolicy : NonlocalPolicy) (outer : List BlockContext) :
      CollectedTree → Except Diagnostic ScopeTree
    | .block context occurrences children => do
      let accesses ← context.mentionedNames.mapM (resolveName nonlocalPolicy context outer)
      let occurrences ← occurrences.mapM (resolveOccurrence context accesses)
      let children ← resolveChildren nonlocalPolicy (context :: outer) children
      let fromChildren := children.flatMap (·.scope.captures)
      let (owned, forwarded) := fromChildren.partition (·.origin == context.path)
      let cells := (owned.map (·.name)).eraseDups
      let captures := (directCaptures accesses ++ forwarded).eraseDups
      return .block ⟨context, accesses, cells, captures, occurrences⟩ children

  private def resolveChildren (nonlocalPolicy : NonlocalPolicy) (outer : List BlockContext) :
      List CollectedTree → Except Diagnostic (List ScopeTree)
    | [] => .ok []
    | child :: rest => do
      return (← resolve nonlocalPolicy outer child) :: (← resolveChildren nonlocalPolicy outer rest)
end

/-- Analyze lexical bindings and closure origins for a constructor-level module. -/
public def analyze (source : Module) (annotationMode : AnnotationMode := .eager)
    (nonlocalPolicy : NonlocalPolicy := .reject) :
    Except Diagnostic ScopeTree := do
  let moduleBlock ← collect { context := { path := [], kind := .module_ }, annotationMode } source.body
  resolve nonlocalPolicy [] moduleBlock.finish

end Silmaril.Languages.Python.Source
