module

public import Silmaril.Languages.Starlark.Modules.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve

open Functions
open Functions.Lowering.Resolve (Context resolveTracked)
open Lists.Iteration (LoopTarget)

/-- Additional clauses with an element expression or a key/value pair. -/
inductive CompTail (Yield : Type) (Operand : Type := Lowering.Resolve.SourceExpr) where
  | yield (value : Yield)
  | filter (test : Operand) (rest : CompTail Yield Operand)
  | forIn (target : Lowering.Resolve.SourceExpr) (iterable : Operand) (rest : CompTail Yield Operand)

def CompTail.operands {Yield Operand : Type} : CompTail Yield Operand → List Operand
  | .yield _ => []
  | .filter test rest => test :: rest.operands
  | .forIn _ iterable rest => iterable :: rest.operands

def CompTail.headValue {Yield Operand : Type} : CompTail Yield Operand → Yield
  | .yield value => value
  | .filter _ rest | .forIn _ _ rest => rest.headValue

private theorem CompTail.headValueSize {Yield Operand : Type} [SizeOf Yield] [SizeOf Operand]
    (tail : CompTail Yield Operand) : sizeOf tail.headValue < sizeOf tail := by
  induction tail <;> simp_all only [headValue, CompTail.yield.sizeOf_spec,
    CompTail.filter.sizeOf_spec, CompTail.forIn.sizeOf_spec] <;> omega

private theorem CompTail.operandSize {Yield Operand : Type} [SizeOf Yield] [SizeOf Operand]
    (tail : CompTail Yield Operand) {operand : Operand} (member : operand ∈ tail.operands) :
    sizeOf operand < sizeOf tail := by
  induction tail with
  | yield => simp [operands] at member
  | filter test rest ih | forIn _ test rest ih =>
    simp only [operands, List.mem_cons] at member
    rcases member with rfl | member
    · simp <;> omega
    · have := ih member
      simp
      omega

abbrev ListCompTail := CompTail Lowering.Resolve.SourceExpr

namespace ListCompTail
export CompTail (yield filter forIn)
end ListCompTail

structure ListComp where
  target : Lowering.Resolve.SourceExpr
  iterable : Lowering.Resolve.SourceExpr
  rest : ListCompTail

structure DictComp where
  target : Lowering.Resolve.SourceExpr
  iterable : Lowering.Resolve.SourceExpr
  rest : CompTail (Lowering.Resolve.SourceExpr × Lowering.Resolve.SourceExpr)

/-- Normalized expression positions that admit comprehension plans. Quotation
of the ordinary expression leaves continues to use the existing grammar. -/
inductive CompExpr where
  | plain (value : Lowering.Resolve.SourceExpr)
  | list (comp : ListComp)
  | dict (comp : DictComp)
  | listClauses (target : Lowering.Resolve.SourceExpr) (iterable : CompExpr)
      (rest : CompTail Lowering.Resolve.SourceExpr CompExpr)
  | dictClauses (target : Lowering.Resolve.SourceExpr) (iterable : CompExpr)
      (rest : CompTail (Lowering.Resolve.SourceExpr × Lowering.Resolve.SourceExpr) CompExpr)
  | listComprehension (target : Lowering.Resolve.SourceExpr) (iterable : CompExpr)
      (rest : CompTail CompExpr CompExpr)
  | dictComprehension (target : Lowering.Resolve.SourceExpr) (iterable : CompExpr)
      (rest : CompTail (CompExpr × CompExpr) CompExpr)
  | listDisplay (elements : List CompExpr)
  | tupleDisplay (elements : List CompExpr)
  | dictDisplay (entries : List (CompExpr × CompExpr))
  | index (receiver subscript : CompExpr)
  | slice (receiver : CompExpr) (start stop stride : Option CompExpr)
  | callPos (callee : Lowering.Resolve.SourceExpr) (arguments : List CompExpr)
  /-- Argument groups are already in valid source order. -/
  | call (callee : CompExpr) (positional : List CompExpr)
      (keywords : List (String × CompExpr)) (star starStar : Option CompExpr)
  | branch (test yes no : CompExpr)
  | logical (op : LogicalOp) (left right : CompExpr)

instance : Coe Lowering.Resolve.SourceExpr CompExpr := ⟨.plain⟩

structure SourceParameter where
  name : String
  defaultExpr : Option CompExpr := none

/-- The AST producer has separated the parameter classes. -/
structure SourceSignature where
  positional : List SourceParameter := []
  keywordOnly : List SourceParameter := []
  varargs : Option String := none
  kwargs : Option String := none

/-- Admitted function statements. -/
inductive Statement where
  | pass
  | assign (name : String) (value : Lowering.Resolve.SourceExpr)
  | assignTarget (target rhs : Lowering.Resolve.SourceExpr)
  | assignTargetCompExpr (target : Lowering.Resolve.SourceExpr) (rhs : CompExpr)
  | assignListComp (name : String) (comp : ListComp)
  | assignDictComp (name : String) (comp : DictComp)
  | assignCompExpr (name : String) (expr : CompExpr)
  | setIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | setIndexCompExpr (receiver subscript rhs : CompExpr)
  | addIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | addIndexCompExpr (receiver subscript rhs : CompExpr)
  | addNameCompExpr (name : String) (rhs : CompExpr)
  | eval (value : Lowering.Resolve.SourceExpr)
  | ret (value : Option Lowering.Resolve.SourceExpr)
  | retCompExpr (value : CompExpr)
  | seq (first rest : Statement)
  | branch (test : Lowering.Resolve.SourceExpr) (yes no : Statement)
  | forIn (target : String) (iterable : Lowering.Resolve.SourceExpr) (body : Statement)
  | forInTarget (target iterable : Lowering.Resolve.SourceExpr) (body : Statement)
  | breakLoop
  | continueLoop
  | define (name : String) (signature : SourceSignature) (body : Statement)

/-- Admitted module commands, in execution order. -/
inductive Command where
  | assign (name : String) (value : Lowering.Resolve.SourceExpr)
  | assignTarget (target rhs : Lowering.Resolve.SourceExpr)
  | assignTargetCompExpr (target : Lowering.Resolve.SourceExpr) (rhs : CompExpr)
  | assignListComp (name : String) (comp : ListComp)
  | assignDictComp (name : String) (comp : DictComp)
  | assignCompExpr (name : String) (expr : CompExpr)
  | setIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | setIndexCompExpr (receiver subscript rhs : CompExpr)
  | addIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | addIndexCompExpr (receiver subscript rhs : CompExpr)
  | eval (value : Lowering.Resolve.SourceExpr)
  | define (name : String) (signature : SourceSignature) (body : Statement)
  | load (label : String) (imports : List Modules.Import)

inductive Error where
  | expression (error : Functions.Lowering.Resolve.Error)
  | validation (error : Modules.Error)
  | emptyLoad (label : String)
  | unsupportedLoopTarget
  | unsupportedAssignmentTarget
  | unsupportedComprehensionTarget
  deriving DecidableEq, Repr

structure ResolvedModule where
  program : Program
  source : Modules.Source

@[expose] def fileNames (commands : List Command) : List String :=
  commands.flatMap fun
    | .load _ imports => imports.map Modules.Import.localName
    | _ => []

/-- Tuple and list spellings share the same resolved sequence target.
The normalized input supplies valid identifier spellings. -/
@[expose] def resolveTarget (slot : String → Binding) (unsupported : Error) :
    Lowering.Resolve.SourceExpr → Except Error (LoopTarget × List String)
  | .scalar (.read name) => pure (.name (slot name), [name])
  | .list elements | .tuple elements => do
    let children ← elements.attach.mapM fun ⟨expr, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      resolveTarget slot unsupported expr
    return (.sequence (children.map Prod.fst), children.flatMap Prod.snd)
  | _ => throw unsupported

@[expose] def parseAssignmentPattern (slot : String → Binding) :
    Lowering.Resolve.SourceExpr →
      Except Error (Comprehensions.AssignmentPattern Lowering.Resolve.SourceExpr × List String)
  | .scalar (.read name) => pure (.name (slot name), [name])
  | .index receiver index => pure (.subscript receiver index, [])
  | .list elements | .tuple elements => do
    let children ← elements.attach.mapM fun ⟨expr, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      parseAssignmentPattern slot expr
    return (.sequence (children.map Prod.fst), children.flatMap Prod.snd)
  | _ => throw .unsupportedAssignmentTarget

/-- Collect the module's lexical scope, including every valid pattern leaf.
Command elaboration rejects invalid targets. -/
@[expose] def globalNames (commands : List Command) : List String :=
  commands.flatMap fun
    | .assign name _ | .assignListComp name _ | .assignDictComp name _
    | .assignCompExpr name _ | .define name .. => [name]
    | .assignTarget target _ =>
      ((resolveTarget globalSlot .unsupportedAssignmentTarget target).toOption.map Prod.snd).getD []
    | .assignTargetCompExpr target _ =>
      ((parseAssignmentPattern globalSlot target).toOption.map Prod.snd).getD []
    | .setIndex .. | .setIndexCompExpr .. | .addIndex .. | .addIndexCompExpr .. | .eval _ | .load .. => []

@[expose] def Statement.localNames : Statement → Except Error (List String)
  | .assign name _ | .assignListComp name _ | .assignDictComp name _
  | .assignCompExpr name _ | .addNameCompExpr name _ | .define name .. => pure [name]
  | .assignTarget target _ =>
    return (← resolveTarget fileSlot .unsupportedAssignmentTarget target).2
  | .assignTargetCompExpr target _ => return (← parseAssignmentPattern fileSlot target).2
  | .seq first rest | .branch _ first rest => return (← first.localNames) ++ (← rest.localNames)
  | .forIn target _ body => return target :: (← body.localNames)
  | .forInTarget target _ body =>
    return (← resolveTarget fileSlot .unsupportedLoopTarget target).2 ++ (← body.localNames)
  | .pass | .setIndex .. | .setIndexCompExpr .. | .addIndex .. | .addIndexCompExpr .. | .eval _ | .ret _ | .retCompExpr _
    | .breakLoop | .continueLoop => pure []

/-- The lexical environment and write scope shared by the mixed assignment
branch and its enclosing module or function compiler. -/
structure BlockContext where
  reads : Context
  writes : Scope

@[expose] def moduleBlock (commands : List Command) : BlockContext :=
  ⟨⟨fileNames commands, globalNames commands⟩, .global⟩

@[expose] def SourceSignature.parameterNames (signature : SourceSignature) : List String :=
  signature.positional.map SourceParameter.name ++ signature.keywordOnly.map SourceParameter.name ++
    signature.varargs.toList ++ signature.kwargs.toList

structure FunctionLayout where
  locals : List String
  block : BlockContext

/-- Compute the local layout after collecting all binder occurrences. Parameters
already have slots, and repeated local assignments share the first slot. -/
@[expose] def functionLayout (parent : Context) (parameters : SourceSignature) (occurrences : List String) :
    FunctionLayout :=
  let names := parameters.parameterNames
  let locals := occurrences.eraseDups.filter (!names.contains ·)
  ⟨locals, ⟨{ parent with locals := (names ++ locals) ++ parent.locals }, .local⟩⟩

@[expose] def collectFunctionLayout (parent : Context) (parameters : SourceSignature) (body : Statement) :
    Except Error FunctionLayout :=
  body.localNames.map (functionLayout parent parameters)

private abbrev Build := StateT Program (Except Error)

private def readExpr (context : Context) (expression : Lowering.Resolve.SourceExpr) :
    Build (Lowering.Expr × List Binding) :=
  monadLift ((resolveTracked context expression).mapError Error.expression)

private def compTarget :=
  resolveTarget fileSlot .unsupportedComprehensionTarget

private def CompTail.names {Yield Operand : Type} : CompTail Yield Operand → Except Error (List String)
  | .yield _ => pure []
  | .filter _ rest => rest.names
  | .forIn target _ rest => return (← compTarget target).2 ++ (← rest.names)

private def compileCompTail {Source Resolved Operand ResolvedOperand : Type}
    (tail : CompTail Source Operand) (readHead : Build (Resolved × List Binding))
    (readOperand : (operand : Operand) → operand ∈ tail.operands → Build (ResolvedOperand × List Binding)) :
    Build (Comprehensions.Tail Resolved ResolvedOperand × List Binding) :=
  match tail with
  | .yield _ => do
    let (value, reads) ← readHead
    return (.yield value, reads)
  | .filter test rest => do
    let (test, reads) ← readOperand test (by simp [CompTail.operands])
    let (rest, restReads) ← compileCompTail rest readHead
      (fun operand member => readOperand operand (List.mem_cons_of_mem _ member))
    return (.filter test rest, reads ++ restReads)
  | .forIn target iterable rest => do
    let (target, _) ← monadLift (compTarget target)
    let (iterable, reads) ← readOperand iterable (by simp [CompTail.operands])
    let (rest, restReads) ← compileCompTail rest readHead
      (fun operand member => readOperand operand (List.mem_cons_of_mem _ member))
    return (.forIn target iterable rest, reads ++ restReads)

private def compileCompWith {Source Resolved Operand ResolvedOperand Comp : Type} (context : Context)
    (pattern : Lowering.Resolve.SourceExpr) (clauses : CompTail Source Operand)
    (readFirst : Context → Build (ResolvedOperand × List Binding))
    (readOperand : Context → (operand : Operand) → operand ∈ clauses.operands →
      Build (ResolvedOperand × List Binding))
    (readHead : Context → Build (Resolved × List Binding))
    (emit : List Binding → LoopTarget → ResolvedOperand → Comprehensions.Tail Resolved ResolvedOperand → Comp) :
    Build (Comp × List Binding) := do
  let (target, firstNames) ← monadLift (compTarget pattern)
  let names := (firstNames ++ (← monadLift clauses.names)).eraseDups
  let locals := names.map fileSlot
  let (iterable, outerReads) ← readFirst context
  let inner := { context with locals := names ++ context.locals }
  let (rest, innerReads) ← compileCompTail clauses (readHead inner) (readOperand inner)
  return (emit locals target iterable rest, outerReads ++ innerReads.filter (!locals.contains ·))

private def compileComp {Source Resolved Comp : Type} (context : Context)
    (pattern operand : Lowering.Resolve.SourceExpr) (clauses : CompTail Source)
    (readYield : Context → Source → Build (Resolved × List Binding))
    (emit : List Binding → LoopTarget → Lowering.Expr → Comprehensions.Tail Resolved → Comp) :
    Build (Comp × List Binding) :=
  compileCompWith context pattern clauses (fun inner => readExpr inner operand)
    (fun inner expr _ => readExpr inner expr) (fun inner => readYield inner clauses.headValue) emit

private def readEntry (context : Context) (entry : Lowering.Resolve.SourceExpr × Lowering.Resolve.SourceExpr) :
    Build ((Lowering.Expr × Lowering.Expr) × List Binding) := do
  let (key, keyReads) ← readExpr context entry.1
  let (value, valueReads) ← readExpr context entry.2
  return ((key, value), keyReads ++ valueReads)

private def compileCompExpr (context : Context) :
    CompExpr → Build (Comprehensions.Expression × List Binding)
  | .plain expression => do
    let (value, reads) ← readExpr context expression
    return (.plain value, reads)
  | .list comp => do
    let (plan, reads) ← compileComp context comp.target comp.iterable comp.rest readExpr Comprehensions.ListComp.mk
    return (.list plan, reads)
  | .dict comp => do
    let (plan, reads) ← compileComp context comp.target comp.iterable comp.rest readEntry Comprehensions.DictComp.mk
    return (.dict plan, reads)
  | .listClauses target iterable rest =>
    compileCompWith context target rest (fun outer => compileCompExpr outer iterable)
      (fun inner operand member =>
        have := rest.operandSize member
        compileCompExpr inner operand)
      (fun inner => readExpr inner rest.headValue) Comprehensions.Expression.listClauses
  | .dictClauses target iterable rest =>
    compileCompWith context target rest (fun outer => compileCompExpr outer iterable)
      (fun inner operand member =>
        have := rest.operandSize member
        compileCompExpr inner operand)
      (fun inner => readEntry inner rest.headValue) Comprehensions.Expression.dictClauses
  | .listComprehension target iterable rest =>
    have headSize := rest.headValueSize
    compileCompWith context target rest (fun outer => compileCompExpr outer iterable)
      (fun inner operand member =>
        have := rest.operandSize member
        compileCompExpr inner operand)
      (fun inner => compileCompExpr inner rest.headValue) Comprehensions.Expression.listComprehension
  | .dictComprehension target iterable rest =>
    have headSize := rest.headValueSize
    have pairSize : sizeOf rest.headValue = 1 + sizeOf rest.headValue.1 + sizeOf rest.headValue.2 := by
      cases rest.headValue <;> rfl
    compileCompWith context target rest (fun outer => compileCompExpr outer iterable)
      (fun inner operand member =>
        have := rest.operandSize member
        compileCompExpr inner operand)
      (fun inner => do
        let (key, keyReads) ← compileCompExpr inner rest.headValue.1
        let (value, valueReads) ← compileCompExpr inner rest.headValue.2
        return ((key, value), keyReads ++ valueReads))
      Comprehensions.Expression.dictComprehension
  | .listDisplay elements => do
    let elements ← elements.attach.mapM fun element => do
      have := List.sizeOf_lt_of_mem element.property
      compileCompExpr context element.val
    return (.listDisplay (elements.map Prod.fst), elements.flatMap Prod.snd)
  | .tupleDisplay elements => do
    let elements ← elements.attach.mapM fun element => do
      have := List.sizeOf_lt_of_mem element.property
      compileCompExpr context element.val
    return (.tupleDisplay (elements.map Prod.fst), elements.flatMap Prod.snd)
  | .dictDisplay entries => do
    let entries ← entries.attach.mapM fun ⟨(key, value), member⟩ => do
      have := (Lowering.entrySize member).1
      have := (Lowering.entrySize member).2
      let (key, keyReads) ← compileCompExpr context key
      let (value, valueReads) ← compileCompExpr context value
      return ((key, value), keyReads ++ valueReads)
    return (.dictDisplay (entries.map Prod.fst), entries.flatMap Prod.snd)
  | .index receiver subscript => do
    let (receiver, receiverReads) ← compileCompExpr context receiver
    let (subscript, subscriptReads) ← compileCompExpr context subscript
    return (.index receiver subscript, receiverReads ++ subscriptReads)
  | .slice receiver start stop stride => do
    let (receiver, receiverReads) ← compileCompExpr context receiver
    let start ← start.attach.mapM fun ⟨operand, member⟩ => do
      have smaller : sizeOf operand < sizeOf start := by simp [Option.mem_def.mp member]
      compileCompExpr context operand
    let stop ← stop.attach.mapM fun ⟨operand, member⟩ => do
      have smaller : sizeOf operand < sizeOf stop := by simp [Option.mem_def.mp member]
      compileCompExpr context operand
    let stride ← stride.attach.mapM fun ⟨operand, member⟩ => do
      have smaller : sizeOf operand < sizeOf stride := by simp [Option.mem_def.mp member]
      compileCompExpr context operand
    let omitted := Comprehensions.Expression.plain (.atom (.scalar .none))
    return (.slice receiver ((start.map Prod.fst).getD omitted) ((stop.map Prod.fst).getD omitted)
      ((stride.map Prod.fst).getD omitted),
      receiverReads ++ (start.toList ++ stop.toList ++ stride.toList).flatMap Prod.snd)
  | .callPos callee arguments => do
    let (callee, calleeReads) ← readExpr context callee
    let compiled ← arguments.attach.mapM fun argument => do
      have := List.sizeOf_lt_of_mem argument.property
      compileCompExpr context argument.val
    return (.callPos callee (compiled.map Prod.fst), calleeReads ++ compiled.flatMap Prod.snd)
  | .call callee positional keywords star starStar => do
    let (callee, calleeReads) ← compileCompExpr context callee
    let positional ← positional.attach.mapM fun ⟨argument, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      compileCompExpr context argument
    let keywords ← keywords.attach.mapM fun ⟨(name, argument), member⟩ => do
      have := (Lowering.entrySize member).2
      return (name, ← compileCompExpr context argument)
    let star ← star.attach.mapM fun ⟨argument, member⟩ => do
      have smaller : sizeOf argument < sizeOf star := by simp [Option.mem_def.mp member]
      compileCompExpr context argument
    let starStar ← starStar.attach.mapM fun ⟨argument, member⟩ => do
      have smaller : sizeOf argument < sizeOf starStar := by simp [Option.mem_def.mp member]
      compileCompExpr context argument
    return (.call callee (positional.map Prod.fst)
      (keywords.map fun (name, argument, _) => (name, argument)) (star.map Prod.fst) (starStar.map Prod.fst),
      calleeReads ++ positional.flatMap Prod.snd ++ keywords.flatMap (·.2.2) ++
        (star.toList ++ starStar.toList).flatMap Prod.snd)
  | .branch test yes no => do
    let (test, tests) ← compileCompExpr context test
    let (yes, yesReads) ← compileCompExpr context yes
    let (no, noReads) ← compileCompExpr context no
    return (.branch test yes no, tests ++ yesReads ++ noReads)
  | .logical op left right => do
    let (left, leftReads) ← compileCompExpr context left
    let (right, rightReads) ← compileCompExpr context right
    return (.logical op left right, leftReads ++ rightReads)
termination_by expr => sizeOf expr
decreasing_by all_goals first | assumption | (simp_wf; omega)

private def resolveSubscript (context : Context) (receiver subscript : Lowering.Resolve.SourceExpr) :
    Build (Lowering.Expr × Lowering.Expr × List Binding) := do
  let (receiver, receiverReads) ← readExpr context receiver
  let (subscript, subscriptReads) ← readExpr context subscript
  return (receiver, subscript, receiverReads ++ subscriptReads)

@[expose] def resolveAssignmentOperands (context : Context) :
    Comprehensions.AssignmentPattern Lowering.Resolve.SourceExpr →
      Except Error (Comprehensions.AssignmentPattern × List Binding)
  | .name binding => pure (.name binding, [])
  | .subscript receiver index => do
    let (receiver, receiverReads) ← (resolveTracked context receiver).mapError Error.expression
    let (index, indexReads) ← (resolveTracked context index).mapError Error.expression
    return (.subscript receiver index, receiverReads ++ indexReads)
  | .sequence children => do
    let children ← children.attach.mapM fun ⟨child, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      resolveAssignmentOperands context child
    return (.sequence (children.map Prod.fst), children.flatMap Prod.snd)

structure ResolvedPatternAssignment where
  pattern : Comprehensions.AssignmentPattern
  rhs : Comprehensions.Expression
  names : List String
  rhsReads : List Binding
  targetReads : List Binding

/-- The RHS phase used by the mixed assignment branch. -/
def elaborateAssignmentRhs (context : Context) (rhs : CompExpr) :
    StateT Program (Except Error) (Comprehensions.Expression × List Binding) :=
  compileCompExpr context rhs

theorem elaborateAssignmentRhs_plain (context : Context) (operand : Lowering.Resolve.SourceExpr)
    (program : Program) :
    elaborateAssignmentRhs context (.plain operand) program =
      ((resolveTracked context operand).mapError Error.expression).map
        (fun (value, reads) => ((.plain value, reads), program)) := by
  unfold elaborateAssignmentRhs
  simp only [compileCompExpr.eq_def, readExpr]
  cases resolveTracked context operand <;> rfl

theorem elaborateAssignmentRhs_list (context : Context) (name : String)
    (iterable element : Lowering.Resolve.SourceExpr) (program : Program) :
    elaborateAssignmentRhs context (.list ⟨.scalar (.read name), iterable, .yield element⟩) program =
      (do
        let (iterated, outer) ← (resolveTracked context iterable).mapError Error.expression
        let inner := { context with locals := name :: context.locals }
        let (emitted, reads) ← (resolveTracked inner element).mapError Error.expression
        return ((.list ⟨[fileSlot name], .name (fileSlot name), iterated, .yield emitted⟩,
          outer ++ reads.filter (fun read => !(fileSlot name == read))), program)) := by
  simp [elaborateAssignmentRhs, compileCompExpr.eq_def, compileComp, compileCompWith, compTarget,
    resolveTarget, CompTail.names, compileCompTail, CompTail.headValue, readExpr,
    show [name].eraseDups = [name] from rfl]
  cases resolveTracked context iterable <;>
    cases resolveTracked { context with locals := name :: context.locals } element <;> rfl

/-- Elaborate a pattern assignment in a supplied lexical block. Module and
function validation remain with the enclosing normalized resolver. -/
@[expose] def elaboratePatternAssignment (context : Context) (scope : Scope)
    (target : Lowering.Resolve.SourceExpr) (rhs : CompExpr) :
    StateT Program (Except Error) ResolvedPatternAssignment := fun program => do
  let (shape, names) ← parseAssignmentPattern (fun name => ⟨scope, name⟩) target
  let ((rhs, rhsReads), next) ← elaborateAssignmentRhs context rhs program
  let (pattern, targetReads) ← resolveAssignmentOperands context shape
  return (⟨pattern, rhs, names, rhsReads, targetReads⟩, next)

private def compileCompAssignment {α : Type} (block : BlockContext)
    (target : Lowering.Resolve.SourceExpr) (rhs : CompExpr)
    (names : LoopTarget → Comprehensions.Expression → α)
    (stores : Comprehensions.AssignmentPattern → Comprehensions.Expression → α) :
    Build (α × List Binding) := do
  match resolveTarget (fun name => ⟨block.writes, name⟩) .unsupportedAssignmentTarget target with
  | .ok (target, _) =>
    let (rhs, reads) ← compileCompExpr block.reads rhs
    return (names target rhs, reads)
  | .error _ =>
    let result ← elaboratePatternAssignment block.reads block.writes target rhs
    return (stores result.pattern result.rhs, result.rhsReads ++ result.targetReads)

private def resolveSetIndex {α : Type} (context : Context)
    (receiver subscript rhs : Lowering.Resolve.SourceExpr)
    (emit : Lowering.Expr → Lowering.Expr → Lowering.Expr → α) : Build (α × List Binding) := do
  let (rhs, rhsReads) ← readExpr context rhs
  let (receiver, subscript, reads) ← resolveSubscript context receiver subscript
  return (emit receiver subscript rhs, rhsReads ++ reads)

private def resolveSetIndexCompExpr {α : Type} (context : Context)
    (receiver subscript rhs : CompExpr)
    (emit : Comprehensions.Expression → Comprehensions.Expression → Comprehensions.Expression → α) :
    Build (α × List Binding) := do
  let (rhs, rhsReads) ← compileCompExpr context rhs
  let (receiver, receiverReads) ← compileCompExpr context receiver
  let (subscript, subscriptReads) ← compileCompExpr context subscript
  return (emit receiver subscript rhs, rhsReads ++ receiverReads ++ subscriptReads)

private def resolveAddIndex {α : Type} (context : Context)
    (receiver subscript rhs : Lowering.Resolve.SourceExpr)
    (emit : Lowering.Expr → Lowering.Expr → Lowering.Expr → α) : Build (α × List Binding) := do
  let (receiver, subscript, reads) ← resolveSubscript context receiver subscript
  let (rhs, rhsReads) ← readExpr context rhs
  return (emit receiver subscript rhs, reads ++ rhsReads)

private def resolveAddIndexCompExpr {α : Type} (context : Context)
    (receiver subscript rhs : CompExpr)
    (emit : Comprehensions.Expression → Comprehensions.Expression → Comprehensions.Expression → α) :
    Build (α × List Binding) := do
  let (receiver, receiverReads) ← compileCompExpr context receiver
  let (subscript, subscriptReads) ← compileCompExpr context subscript
  let (rhs, rhsReads) ← compileCompExpr context rhs
  return (emit receiver subscript rhs, receiverReads ++ subscriptReads ++ rhsReads)

private structure ResolvedParameter where
  slot : Binding
  value : Option Comprehensions.Expression
  reads : List Binding

private def readParameter (context : Context) (parameter : SourceParameter) : Build ResolvedParameter := do
  let slot := fileSlot parameter.name
  match parameter.defaultExpr with
  | none => return ⟨slot, none, []⟩
  | some expression =>
    let (value, reads) ← compileCompExpr context expression
    return ⟨slot, some value, reads⟩

private def ResolvedParameter.plain (parameter : ResolvedParameter) : Option Functions.Parameter :=
  match parameter.value with
  | none => some ⟨parameter.slot, none⟩
  | some (.plain expression) => some ⟨parameter.slot, some expression⟩
  | some _ => none

private def ResolvedParameter.staged (parameter : ResolvedParameter) : Functions.Parameter :=
  ⟨parameter.slot, parameter.value.map fun _ =>
    .atom (Comprehensions.readSaved (Comprehensions.defaultSlot parameter.slot))⟩

structure ResolvedBody where
  code : Body
  reads : List Binding

@[expose] def captureNames (owned : List String) (reads : List Binding) : List FreeName :=
  (reads.eraseDups.filter fun binding => binding.scope == .global || !owned.contains binding.name).map
    fun binding => ⟨binding, binding⟩

private def compileDefinition (parent : Context) (parameters : SourceSignature) (layout : FunctionLayout)
    (compile : BlockContext → Build ResolvedBody) :
    Build (DeclarationId × Option (List (Binding × Comprehensions.Expression)) × List Binding) := do
  let positional ← parameters.positional.mapM (readParameter parent)
  let keywords ← parameters.keywordOnly.mapM (readParameter parent)
  let named := positional ++ keywords
  let (positionalSlots, keywordSlots, stagedDefaults) :=
    match positional.mapM ResolvedParameter.plain, keywords.mapM ResolvedParameter.plain with
    | some ps, some ks => (ps, ks, none)
    | _, _ =>
      (positional.map ResolvedParameter.staged, keywords.map ResolvedParameter.staged,
        some (named.filterMap fun parameter => parameter.value.map (parameter.slot, ·)))
  let signature : Functions.Signature :=
    ⟨positionalSlots, keywordSlots,
    parameters.varargs.map fileSlot, parameters.kwargs.map fileSlot⟩
  let body ← compile layout.block
  let captures := captureNames (parameters.parameterNames ++ layout.locals) body.reads
  let program ← get
  set (program.push ⟨signature, layout.locals.map fileSlot, captures, body.code⟩)
  -- A child needs its captures when it is defined. Its defaults also read the parent.
  return (program.size, stagedDefaults, named.flatMap ResolvedParameter.reads ++ captures.map FreeName.source)

def compileBody (block : BlockContext) (statement : Statement) : StateT Program (Except Error) ResolvedBody :=
  let context := block.reads
  match statement with
  | .pass => pure ⟨.total (.atomic .pass), []⟩
  | .assign name value => do
    let (value, reads) ← readExpr context value
    return ⟨.assignExpr (fileSlot name) value, reads⟩
  | .assignTarget target rhs => do
    let (target, _) ← monadLift (resolveTarget fileSlot .unsupportedAssignmentTarget target)
    let (rhs, reads) ← readExpr context rhs
    return ⟨.assignTargetExpr target rhs, reads⟩
  | .assignTargetCompExpr target rhs => do
    let (code, reads) ← compileCompAssignment block target rhs
      (fun target rhs => rhs.assignTargetCode target Comprehensions.directStages)
      (fun target rhs => Comprehensions.assignPatternCode target rhs Comprehensions.directStages)
    return ⟨code, reads⟩
  | .assignListComp name comp => do
    let (comp, reads) ← compileComp context comp.target comp.iterable comp.rest readExpr Comprehensions.ListComp.mk
    return ⟨comp.body (fileSlot name), reads⟩
  | .assignDictComp name comp => do
    let (comp, reads) ← compileComp context comp.target comp.iterable comp.rest readEntry Comprehensions.DictComp.mk
    return ⟨comp.body (fileSlot name), reads⟩
  | .assignCompExpr name expr => do
    let (expr, reads) ← compileCompExpr context expr
    return ⟨expr.body (fileSlot name), reads⟩
  | .setIndex receiver subscript rhs => do
    let (code, reads) ← resolveSetIndex context receiver subscript rhs Body.setIndexExpr
    return ⟨code, reads⟩
  | .setIndexCompExpr receiver subscript rhs => do
    let (code, reads) ← resolveSetIndexCompExpr context receiver subscript rhs fun receiver subscript rhs =>
      Comprehensions.setIndexCode receiver subscript rhs Comprehensions.directStages
    return ⟨code, reads⟩
  | .addIndex receiver subscript rhs => do
    let (code, reads) ← resolveAddIndex context receiver subscript rhs Body.addIndexExpr
    return ⟨code, reads⟩
  | .addIndexCompExpr receiver subscript rhs => do
    let (code, reads) ← resolveAddIndexCompExpr context receiver subscript rhs fun receiver subscript rhs =>
      Comprehensions.addIndexCode receiver subscript rhs Comprehensions.directStages
    return ⟨code, reads⟩
  | .addNameCompExpr name rhs => do
    let (rhs, reads) ← compileCompExpr context rhs
    return ⟨Comprehensions.addNameCode (fileSlot name) rhs Comprehensions.directStages, reads⟩
  | .eval value => do
    let (value, reads) ← readExpr context value
    return ⟨.evalExpr value, reads⟩
  | .ret none => pure ⟨.returnExpr (.atom (.scalar .none)), []⟩
  | .ret (some value) => do
    let (value, reads) ← readExpr context value
    return ⟨.returnExpr value, reads⟩
  | .retCompExpr expr => do
    let (expr, reads) ← compileCompExpr context expr
    return ⟨expr.returnCode Comprehensions.directStages, reads⟩
  | .seq first rest => do
    let first ← compileBody block first
    let rest ← compileBody block rest
    return ⟨.seq first.code rest.code, first.reads ++ rest.reads⟩
  | .branch test yes no => do
    let (test, reads) ← readExpr context test
    let yes ← compileBody block yes
    let no ← compileBody block no
    return ⟨.branchExpr test yes.code no.code, reads ++ yes.reads ++ no.reads⟩
  | .forIn target iterable body => do
    let (iterable, reads) ← readExpr context iterable
    let body ← compileBody block body
    return ⟨.forInExpr (fileSlot target) iterable body.code, reads ++ body.reads⟩
  | .forInTarget target iterable body => do
    let (target, _) ← monadLift (resolveTarget fileSlot .unsupportedLoopTarget target)
    let (iterable, reads) ← readExpr context iterable
    let body ← compileBody block body
    return ⟨.forInExpr target iterable body.code, reads ++ body.reads⟩
  | .breakLoop => pure ⟨.breakLoop, []⟩
  | .continueLoop => pure ⟨.continueLoop, []⟩
  | .define name signature body => do
    let layout ← monadLift (collectFunctionLayout context signature body)
    let (id, defaults, reads) ←
      compileDefinition context signature layout (fun inner => compileBody inner body)
    let target := fileSlot name
    let code := defaults.elim (.define target id)
      (Comprehensions.definitionWithDefaults Comprehensions.directStages target id)
    return ⟨code, reads⟩
termination_by structural statement

/-- A required positional signature has no definition-time operands. -/
@[expose] def SourceSignature.required (names : List String) : SourceSignature :=
  { positional := names.map fun name => ⟨name, none⟩ }

@[expose] def requiredSignature (names : List String) : Functions.Signature :=
  { positional := names.map fun name => ⟨fileSlot name, none⟩ }

private theorem lift_ok {α : Type} (value : α) (program : Program) :
    (monadLift (Except.ok value : Except Error α) : Build α) program = .ok (value, program) := rfl

private theorem get_build (program : Program) : (get : Build Program) program = .ok (program, program) := rfl

private theorem set_build (before after : Program) : (set after : Build Unit) before = .ok ((), after) := rfl

private def requiredParameter (name : String) : ResolvedParameter := ⟨fileSlot name, none, []⟩

private theorem read_required (context : Context) (names : List String) (program : Program) :
    (names.mapM (readParameter context ∘ fun name => ⟨name, none⟩)) program =
      .ok (names.map requiredParameter, program) := by
  change (names.mapM fun name => pure (requiredParameter name) : Build (List ResolvedParameter)) program = _
  rw [List.mapM_pure]
  rfl

private theorem plain_required (names : List String) :
    names.mapM (ResolvedParameter.plain ∘ requiredParameter) =
      some (names.map fun name => (⟨fileSlot name, none⟩ : Functions.Parameter)) := by
  change names.mapM (fun name => pure (⟨fileSlot name, none⟩ : Functions.Parameter)) = _
  rw [List.mapM_pure]
  rfl

private theorem required_reads (names : List String) :
    (names.map requiredParameter).flatMap ResolvedParameter.reads = [] := by
  simp [List.flatMap_map, requiredParameter]

private theorem required_names (names : List String) :
    ({ positional := names.map fun name => ⟨name, none⟩ } : SourceSignature).parameterNames = names := by
  simp [SourceSignature.parameterNames, Function.comp_def]

private theorem rejectMixedTarget (scope : Scope) (name : String)
    (receiver index : Lowering.Resolve.SourceExpr) :
    resolveTarget (fun name => ⟨scope, name⟩) .unsupportedAssignmentTarget
      (.tuple [.scalar (.read name), .index receiver index]) = .error .unsupportedAssignmentTarget := by
  simp [resolveTarget, List.mapM_cons, bind, Except.bind, pure, Except.pure] <;> rfl

theorem compileBody_mixedReturn (block : BlockContext) (name : String)
    (receiver index returned : Lowering.Resolve.SourceExpr) (rhs : CompExpr)
    (program next : Program) (assignment : ResolvedPatternAssignment) (value : Lowering.Expr)
    (reads : List Binding)
    (resolved : elaboratePatternAssignment block.reads block.writes
      (.tuple [.scalar (.read name), .index receiver index]) rhs program = .ok (assignment, next))
    (returnResolved : resolveTracked block.reads returned = .ok (value, reads)) :
    compileBody block (.seq (.assignTargetCompExpr (.tuple [.scalar (.read name), .index receiver index]) rhs)
      (.ret (some returned))) program =
      .ok (⟨.seq (Comprehensions.assignPatternCode assignment.pattern assignment.rhs Comprehensions.directStages)
        (.returnExpr value), (assignment.rhsReads ++ assignment.targetReads) ++ reads⟩, next) := by
  simp [compileBody, compileCompAssignment, rejectMixedTarget, readExpr, bind, StateT.bind, lift_ok,
    returnResolved, resolved, Except.mapError, Except.bind, pure, StateT.pure, Except.pure]

theorem compileBody_seqReturn (block : BlockContext) (first : Statement)
    (returned : Lowering.Resolve.SourceExpr) (program next : Program) (resolved : ResolvedBody)
    (value : Lowering.Expr) (reads : List Binding)
    (compiled : compileBody block first program = .ok (resolved, next))
    (returnResolved : resolveTracked block.reads returned = .ok (value, reads)) :
    compileBody block (.seq first (.ret (some returned))) program =
      .ok (⟨.seq resolved.code (.returnExpr value), resolved.reads ++ reads⟩, next) := by
  simp [compileBody, readExpr, bind, StateT.bind, lift_ok, returnResolved, compiled, Except.mapError,
    Except.bind, pure, StateT.pure, Except.pure]

theorem compileBody_requiredDefinition (parent : BlockContext) (name : String) (parameters : List String)
    (body : Statement) (program next : Program) (layout : FunctionLayout) (resolved : ResolvedBody)
    (collected : collectFunctionLayout parent.reads (.required parameters) body = .ok layout)
    (compiled : compileBody layout.block body program = .ok (resolved, next)) :
    let captures := captureNames (parameters ++ layout.locals) resolved.reads
    compileBody parent (.define name (.required parameters) body) program =
      .ok (⟨.define (fileSlot name) next.size, captures.map FreeName.source⟩,
        next.push ⟨requiredSignature parameters, layout.locals.map fileSlot, captures, resolved.code⟩) := by
  simp only [SourceSignature.required] at collected
  simp [compileBody, collected, compileDefinition, SourceSignature.required, required_names,
    bind, StateT.bind, lift_ok, get_build, set_build, read_required, plain_required, required_reads,
    Except.bind, pure, StateT.pure, Except.pure, compiled, requiredSignature]

/-- Elaborate one normalized command in the module-wide lexical context. -/
def elaborateCommand (block : BlockContext) (command : Command) :
    StateT Program (Except Error) Modules.Command :=
  let context := block.reads
  match command with
  | .assign name value => do
    let (value, _) ← readExpr context value
    return .exec (.assignExpr name value)
  | .assignTarget target rhs => do
    let (target, _) ← monadLift (resolveTarget globalSlot .unsupportedAssignmentTarget target)
    let (rhs, _) ← readExpr context rhs
    return .exec (.assignTargetExpr target rhs)
  | .assignTargetCompExpr target rhs => do
    let (code, _) ← compileCompAssignment block target rhs
      TopCode.assignTargetCompExpr TopCode.assignPatternCompExpr
    return .exec code
  | .assignListComp name comp => do
    let (comp, _) ← compileComp context comp.target comp.iterable comp.rest readExpr Comprehensions.ListComp.mk
    return .exec (.assignListComp name comp)
  | .assignDictComp name comp => do
    let (comp, _) ← compileComp context comp.target comp.iterable comp.rest readEntry Comprehensions.DictComp.mk
    return .exec (.assignDictComp name comp)
  | .assignCompExpr name expr => do
    let (expr, _) ← compileCompExpr context expr
    return .exec (.assignCompExpr name expr)
  | .setIndex receiver subscript rhs => do
    let (code, _) ← resolveSetIndex context receiver subscript rhs TopCode.setIndexExpr
    return .exec code
  | .setIndexCompExpr receiver subscript rhs => do
    let (code, _) ← resolveSetIndexCompExpr context receiver subscript rhs TopCode.setIndexCompExpr
    return .exec code
  | .addIndex receiver subscript rhs => do
    let (code, _) ← resolveAddIndex context receiver subscript rhs TopCode.addIndexExpr
    return .exec code
  | .addIndexCompExpr receiver subscript rhs => do
    let (code, _) ← resolveAddIndexCompExpr context receiver subscript rhs TopCode.addIndexCompExpr
    return .exec code
  | .eval value => do
    let (value, _) ← readExpr context value
    return .exec (.evalExpr value)
  | .define name signature body => do
    let layout ← monadLift (collectFunctionLayout context signature body)
    let (id, defaults, _) ←
      compileDefinition context signature layout (fun inner => compileBody inner body)
    return .exec (defaults.elim (.define name id) (.defineWithDefaults name id))
  | .load label imports =>
    if imports.isEmpty then throw (.emptyLoad label) else pure (.load label imports)

theorem elaborateCommand_assign (block : BlockContext) (name : String) (value : Lowering.Resolve.SourceExpr)
    (program : Program) :
    elaborateCommand block (.assign name value) program =
      ((resolveTracked block.reads value).mapError Error.expression).map
        (fun (code, _) => (.exec (.assignExpr name code), program)) := by
  cases operand : resolveTracked block.reads value <;>
    simp [elaborateCommand, readExpr, operand, Except.mapError, bind, StateT.bind, Except.bind, lift_ok, pure, StateT.pure, Except.map] <;> rfl

theorem elaborateCommand_eval (block : BlockContext) (value : Lowering.Resolve.SourceExpr) (program : Program) :
    elaborateCommand block (.eval value) program =
      ((resolveTracked block.reads value).mapError Error.expression).map
        (fun (code, _) => (.exec (.evalExpr code), program)) := by
  cases operand : resolveTracked block.reads value <;>
    simp [elaborateCommand, readExpr, operand, Except.mapError, bind, StateT.bind, Except.bind, lift_ok, pure, StateT.pure, Except.map] <;> rfl

theorem elaborateCommand_requiredDefinition (block : BlockContext) (writes : Scope) (name : String) (parameters : List String)
    (body : Statement) (program next : Program) (id : DeclarationId) (reads : List Binding)
    (compiled : compileBody block (.define name (.required parameters) body) program =
      .ok (⟨.define (fileSlot name) id, reads⟩, next)) :
    elaborateCommand { block with writes } (.define name (.required parameters) body) program =
      .ok (.exec (.define name id), next) := by
  cases layoutEq : collectFunctionLayout block.reads (.required parameters) body with
  | error error =>
    simp only [SourceSignature.required] at layoutEq
    simp [compileBody, layoutEq, bind, StateT.bind, Except.bind, SourceSignature.required] at compiled
    exact nomatch compiled
  | ok layout =>
    simp only [SourceSignature.required] at layoutEq
    cases inner : compileBody layout.block body program <;>
      simp_all [compileBody, elaborateCommand, compileDefinition, SourceSignature.required, required_names,
        bind, StateT.bind, lift_ok, get_build, set_build, read_required, plain_required, required_reads,
        Except.bind, pure, StateT.pure, Except.pure]

/-- One resolved plain default together with its normalized source and reads. -/
structure PlainPositionalDefault where
  name : String
  source : Lowering.Resolve.SourceExpr
  value : Lowering.Expr
  reads : List Binding

@[expose] def PlainPositionalDefault.parameter (item : PlainPositionalDefault) : SourceParameter :=
  ⟨item.name, some (.plain item.source)⟩

@[expose] def PlainPositionalDefault.resolved (item : PlainPositionalDefault) : Functions.Parameter :=
  ⟨fileSlot item.name, some item.value⟩

private theorem read_plain_positionals (context : Context) (parameters : List PlainPositionalDefault)
    (checked : ∀ item ∈ parameters, resolveTracked context item.source = .ok (item.value, item.reads))
    (program : Program) :
    ((parameters.map PlainPositionalDefault.parameter).mapM (readParameter context)) program =
      .ok (parameters.map (fun item => ⟨fileSlot item.name, some (.plain item.value), item.reads⟩), program) := by
  induction parameters with
  | nil => rfl
  | cons head rest ih =>
    have read := checked head List.mem_cons_self
    have tail := ih (fun item present => checked item (List.mem_cons_of_mem _ present))
    simp only [List.map_cons, List.mapM_cons]
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]
    have headRead : readParameter context head.parameter program =
        .ok (⟨fileSlot head.name, some (.plain head.value), head.reads⟩, program) := by
      simp [readParameter, PlainPositionalDefault.parameter, compileCompExpr.eq_def, readExpr,
        bind, StateT.bind, Except.bind, lift_ok, read, Except.mapError, pure, StateT.pure, Except.pure]
    simp [headRead, tail]

private theorem plain_optional (parameters : List PlainPositionalDefault) :
    (parameters.map (fun item : PlainPositionalDefault =>
      (⟨fileSlot item.name, some (.plain item.value), item.reads⟩ : ResolvedParameter))).mapM ResolvedParameter.plain =
        some (parameters.map PlainPositionalDefault.resolved) := by
  rw [List.mapM_map]
  change (parameters.mapM fun item => pure item.resolved) = _
  rw [List.mapM_pure]
  rfl

/-- Plain positional defaults leave their direct expressions in the emitted
signature, using the defining context. The definition command stays native. -/
theorem elaborateCommand_plainPositionalDefinition (block : BlockContext) (name : String) (required : List String)
    (defaults : List PlainPositionalDefault) (body : Statement) (program next : Program)
    (layout : FunctionLayout) (compiled : ResolvedBody)
    (closed : ∀ item ∈ defaults, resolveTracked block.reads item.source = .ok (item.value, item.reads))
    (collected : collectFunctionLayout block.reads
      { positional := required.map (fun name => ⟨name, none⟩) ++ defaults.map PlainPositionalDefault.parameter } body =
      .ok layout)
    (bodyCode : compileBody layout.block body program = .ok (compiled, next)) :
    let source : SourceSignature :=
      { positional := required.map (fun name => ⟨name, none⟩) ++ defaults.map PlainPositionalDefault.parameter }
    let signature : Functions.Signature :=
      { positional := (requiredSignature required).positional ++ defaults.map PlainPositionalDefault.resolved }
    let captures := captureNames (source.parameterNames ++ layout.locals) compiled.reads
    elaborateCommand block (.define name source body) program =
      .ok (.exec (.define name next.size), next.push ⟨signature, layout.locals.map fileSlot, captures, compiled.code⟩) := by
  have optionalRead := read_plain_positionals block.reads defaults closed program
  rw [List.mapM_map] at optionalRead
  have optionalPlain := plain_optional defaults
  rw [List.mapM_map] at optionalPlain
  have requiredPlain := plain_required required
  simp [elaborateCommand, collected, compileDefinition, List.mapM_append, List.mapM_map,
    read_required, optionalRead, requiredPlain, optionalPlain, requiredSignature,
    bind, StateT.bind, Except.bind, lift_ok, get_build, set_build, pure, StateT.pure, Except.pure, bodyCode]

/-- The same plain defaults in a function body emit a direct definition
and propagate their defining-scope reads to the containing declaration. -/
theorem compileBody_plainPositionalDefinition (block : BlockContext) (name : String) (required : List String)
    (defaults : List PlainPositionalDefault) (body : Statement) (program next : Program)
    (layout : FunctionLayout) (compiled : ResolvedBody)
    (closed : ∀ item ∈ defaults, resolveTracked block.reads item.source = .ok (item.value, item.reads))
    (collected : collectFunctionLayout block.reads
      { positional := required.map (fun name => ⟨name, none⟩) ++ defaults.map PlainPositionalDefault.parameter } body =
      .ok layout)
    (bodyCode : compileBody layout.block body program = .ok (compiled, next)) :
    let source : SourceSignature :=
      { positional := required.map (fun name => ⟨name, none⟩) ++ defaults.map PlainPositionalDefault.parameter }
    let signature : Functions.Signature :=
      { positional := (requiredSignature required).positional ++ defaults.map PlainPositionalDefault.resolved }
    let captures := captureNames (source.parameterNames ++ layout.locals) compiled.reads
    compileBody block (.define name source body) program =
      .ok (⟨.define (fileSlot name) next.size, defaults.flatMap PlainPositionalDefault.reads ++ captures.map FreeName.source⟩,
        next.push ⟨signature, layout.locals.map fileSlot, captures, compiled.code⟩) := by
  have optionalRead := read_plain_positionals block.reads defaults closed program
  rw [List.mapM_map] at optionalRead
  have optionalPlain := plain_optional defaults
  rw [List.mapM_map] at optionalPlain
  simp [compileBody, collected, compileDefinition, List.mapM_append, List.mapM_map,
    read_required, optionalRead, plain_required, requiredSignature, required_reads, optionalPlain,
    bind, StateT.bind, Except.bind, lift_ok, get_build, set_build, pure, StateT.pure, Except.pure, bodyCode]
  simp [List.flatMap_map]

theorem compileBody_plainAssign (block : BlockContext) (name : String) (source : Lowering.Resolve.SourceExpr)
    (value : Lowering.Expr) (reads : List Binding) (program : Program)
    (operand : resolveTracked block.reads source = .ok (value, reads)) :
    compileBody block (.assign name source) program = .ok (⟨.assignExpr (fileSlot name) value, reads⟩, program) := by
  simp [compileBody, readExpr, operand, Except.mapError, bind, StateT.bind, Except.bind, lift_ok, pure, StateT.pure, Except.pure]

theorem compileBody_plainSeq (block : BlockContext) (first rest : Statement) (program middle final : Program)
    (head tail : ResolvedBody)
    (compiled : compileBody block first program = .ok (head, middle))
    (remaining : compileBody block rest middle = .ok (tail, final)) :
    compileBody block (.seq first rest) program = .ok (⟨.seq head.code tail.code, head.reads ++ tail.reads⟩, final) := by
  simp [compileBody, compiled, remaining, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

/-- A plain return reads its operand in the collected function context. -/
theorem compileBody_plainReturn (block : BlockContext) (source : Lowering.Resolve.SourceExpr)
    (value : Lowering.Expr) (reads : List Binding) (program : Program)
    (operand : resolveTracked block.reads source = .ok (value, reads)) :
    compileBody block (.ret (some source)) program = .ok (⟨.returnExpr value, reads⟩, program) := by
  simp [compileBody, readExpr, operand, Except.mapError, bind, StateT.bind, Except.bind, lift_ok, pure, StateT.pure, Except.pure]

/-- Elaborate in source order, appending declarations to the supplied linked
table. Call `resolve` for checked intake. -/
@[expose] def elaborateCommands (commands : List Command) (linked : Program := #[]) :
    Except Error (List Modules.Command × Program) :=
  (commands.mapM (elaborateCommand (moduleBlock commands))) linked

/-- A leading expression statement keeps its position in checked command order. -/
theorem elaborateCommands_eval_cons (value : Lowering.Resolve.SourceExpr) (rest : List Command)
    (linked : Program) (code : Lowering.Expr) (reads : List Binding)
    (operand : resolveTracked (moduleBlock (.eval value :: rest)).reads value = .ok (code, reads))
    (commands : List Modules.Command) (program : Program)
    (checked : elaborateCommands (.eval value :: rest) linked = .ok (commands, program)) :
    ∃ suffix, commands = .exec (.evalExpr code) :: suffix := by
  simp only [elaborateCommands, List.mapM_cons, elaborateCommand, readExpr, operand, bind, StateT.bind,
    lift_ok, pure, StateT.pure, Except.mapError, Except.bind, Except.pure] at checked
  split at checked <;> simp_all <;> exact ⟨_, checked.1.symm⟩

/-- Elaborate and validate the emitted declaration table and commands.
Input names are normalized identifiers. -/
@[expose] def resolve (commands : List Command) (linked : Program := #[]) : Except Error ResolvedModule :=
  match elaborateCommands commands linked with
  | .error error => .error error
  | .ok (code, program) =>
    let source : Modules.Source := ⟨globalNames commands, [], code⟩
    match validateSource program source with
    | .error error => .error (.validation error)
    | .ok () => .ok ⟨program, source⟩

abbrev Result := Except Error (Modules.Result Published)

/-- Static rejection is separate from execution. Successful elaboration uses
the resolved module evaluator. When catalog values can contain closures,
supply their original heap and linked declarations. -/
@[expose] def runModule (commands : List Command) (host : Catalog) (caller : Lists.State)
    (linked : Program := #[]) : Result :=
  match resolve commands linked with
  | .error error => .error error
  | .ok resolved => .ok (initializeModule resolved.program host resolved.source caller)

end Silmaril.Languages.Starlark.Modules.Resolve
