module

public import Silmaril.Cerberus.Elaboration.Expressions.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs
public import Silmaril.Cerberus.Elaboration.LocalObjects.Defs
public import Silmaril.Cerberus.Elaboration.Scheduling.Defs
public import Silmaril.Cerberus.Elaboration.ControlFlow.Defs
public import Silmaril.Cerberus.Elaboration.LoopControl.Defs
public import Silmaril.Cerberus.Elaboration.Loops.Defs

/-! Focused actual `translation.lem` statement cases: skip, automatic-object
blocks, arithmetic local initialization, integer conditionals/while loops, labels
and lifetime-aware goto transfers, discarded integer/void expressions and integer
returns and direct non-CHERI pointer/null returns with local lifetime kills. Break/continue are erased by the pinned prior pass. The expression stage is separate. Other statement and
lifetime obligations reject explicitly. No C0
interpreter or observed result is used to construct these Core expressions. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Statements
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

structure Environment where
  returnType : Ctype
  returnLabel : Sym
  noreturn : Bool

/-- Source `mk_unit_sseq`, including the final skip even after a return. -/
def unitSequence (expressions : List Effect) (continuation : Effect) : Effect :=
  expressions.foldr (fun expression rest => strongSequence (wildcard .unit) expression rest) continuation

/-- This focused subset has no object kills or creations across a transfer. -/
def emptyLifetimeRun (label : Sym) (arguments : List Pure) : State.ElabM Effect := do
  let visible ← State.getVisibleObjects
  unless visible.isEmpty do
    throw (.message "statement translation with live object lifetimes is not ported")
  return Construction.run label arguments

def liftError {α : Type} : Except String α → State.ElabM α
  | .ok value => pure value
  | .error why => throw (.message why)

def integerType : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | .mk _ (.atomic type) => integerType type
  | _ => false

/-- Pinned AilSexpr discards the translated value, then yields unit. This
focused branch admits direct integer/void result types only; unsupported
expression nodes still reject in the actual expression translator. The
currently admitted nodes have no used-value-dependent lowering equation. -/
def expressionStatement (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (expression : Ail.TypedExpression)
    (aliases : Designators.Aliases) : State.ElabM Effect := do
  let type ← liftError <| (GeneralizedTypes.expressionType config types expression).mapError reprStr
  let resultType ← match type with
    | .mk _ .void => pure BaseType.unit
    | .mk _ (.basic (.integer _)) => pure (BaseType.loaded .integer)
    | .mk _ (.pointer ..) => pure (BaseType.loaded .pointer)
    | _ => throw (.message "expression statement result type is not ported")
  let core ← Expressions.wrappedExpression config types runtime expression aliases
  return strongSequence (wildcard resultType) core (pureEffect Construction.unit)

/-- The upstream integer return branch retains the source return Ctype,
including its locations, as the argument to `conv_loaded_int`. -/
def returnExpression (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (expression : Ail.TypedExpression) (statementLocation : Loc := .unknown)
    (aliases : Designators.Aliases := []) : State.ElabM Effect := do
  if environment.noreturn then
    throw (.message "noreturn statement elaboration is not ported")
  let visible ← Lifetimes.captureVisible
  -- Pinned translation.lem:3908–3911: no child translation or fresh wrapper
  -- occurs on the null-pointer-constant return fast path. The complete return
  -- CType, annotations and lifetime transfer are retained exactly as upstream.
  if Constants.isPointer environment.returnType then
    if config.cheri then throw (.message "unsupported: CHERI pointer return")
    if NullPointers.isNullPointerConstant expression then
      let value := specified (nullptr environment.returnType)
      if visible.isEmpty then return ← emptyLifetimeRun environment.returnLabel [value]
      else return Lifetimes.returnRun statementLocation environment.returnLabel visible [value]
    -- Pinned translation.lem:3913–3946: pointer returns use the unchanged
    -- loaded value; only arithmetic results use conv_loaded_arith. Unsupported
    -- nonpointer conversions and pointer-to-Bool remain explicit rejections.
    let sourceType ← liftError <| (GeneralizedTypes.expressionType config types expression).mapError reprStr
    unless Constants.isPointer sourceType do
      throw (.message "unsupported: pointer return from nonpointer expression")
    let core ← Expressions.wrappedExpression config types runtime expression aliases
    let temporary ← State.wrappedFreshSymbol (.loaded .pointer)
    let transfer ← if visible.isEmpty then emptyLifetimeRun environment.returnLabel [temporary.expression]
      else pure (Lifetimes.returnRun statementLocation environment.returnLabel visible [temporary.expression])
    return strongSequence temporary.pattern core transfer
  let sourceType ← liftError <| (GeneralizedTypes.expressionType config types expression).mapError reprStr
  unless integerType sourceType && integerType environment.returnType do
    throw (.message "noninteger return elaboration is not ported")
  let core ← Expressions.wrappedExpression config types runtime expression aliases
  let temporary ← State.wrappedFreshSymbol (.loaded .integer)
  let value ← liftError <| Conversion.loadedArithmetic runtime sourceType environment.returnType temporary.expression
  let transfer ← if visible.isEmpty then emptyLifetimeRun environment.returnLabel [value]
    else pure (Lifetimes.returnRun statementLocation environment.returnLabel visible [value])
  return strongSequence temporary.pattern core transfer

/-- Source annotation wrapper is independent of construction-time freshness. -/
def annotate (statement : Ail.TypedStatement) (core : Effect) : Effect :=
  let .mk location _ attributes _ := statement
  addLocation location (addStatement (addAttributes attributes core))

/-- Construct the raw node action before executing it. Sibling block actions
are constructed in the pinned source map order; bind continuations, including
nested if branches, are constructed when reached during execution. -/
def construct (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (statement : Ail.TypedStatement) (sourceFunction : Option Sym := none)
    (aliases : Designators.Aliases := []) (labelVisibles : LoopControl.Labels := []) : Scheduling.Computation Effect :=
  let .mk location _ _ node := statement
  match _hnode : node with
  | .skip => Scheduling.defer (pure skip)
  | .expr expression => Scheduling.defer
      (expressionStatement config types runtime expression aliases)
  | .return_ expression => Scheduling.defer
      (returnExpression config types runtime environment expression location aliases)
  | .block bindings statements =>
      (do
        let children ← Scheduling.mapM (fun (child : { item : Ail.TypedStatement // item ∈ statements }) =>
          Scheduling.map (annotate child.val)
            (construct config types runtime environment child.val sourceFunction aliases labelVisibles)) statements.attach
        return (if bindings.isEmpty then do
          let (_, compoundLiterals, translated) ← State.withBlockObjects [] children
          unless compoundLiterals.isEmpty do
            throw (.message "block compound-literal lifetimes are not ported")
          return unitSequence translated skip
        else do
          let some functionSymbol := sourceFunction
            | throw (.message "local-object block requires its actual source function symbol")
          LocalObjects.block config functionSymbol location bindings children : State.ElabM Effect)
        : Scheduling.Build (State.ElabM Effect))
  | .declaration inputs => Scheduling.defer
      (LocalObjects.initializers config types runtime location
        (fun input => Expressions.wrappedExpression config types runtime input aliases) inputs)
  | .if_ condition yes no =>
      Scheduling.bind (Scheduling.wrappedFreshSymbol .boolean) fun prepared =>
        Scheduling.defer (ControlFlow.integerIf config types prepared location condition
          (fun _ input => Expressions.wrappedExpression config types runtime input aliases)
          (annotate yes <$> Scheduling.execute
            (construct config types runtime environment yes sourceFunction aliases labelVisibles))
          (annotate no <$> Scheduling.execute
            (construct config types runtime environment no sourceFunction aliases labelVisibles)))
  | .while_ condition body loopId =>
      (do
        let freshness : Freshness.Context ← get
        let loopSymbol ← Scheduling.freshDescription (.id s!"while_{freshness.next}")
        let preparedAction ← Scheduling.wrappedFreshSymbol .boolean
        return (do
          let prepared ← preparedAction
          Loops.integerWhile config types loopSymbol prepared location condition loopId
            (fun _ input => Expressions.wrappedExpression config types runtime input aliases)
            (annotate body <$> Scheduling.execute
              (construct config types runtime environment body sourceFunction aliases labelVisibles))
          : State.ElabM Effect) : Scheduling.Build (State.ElabM Effect))
  | .label label body annotation => Scheduling.defer do
      let coreBody ← annotate body <$> Scheduling.execute
        (construct config types runtime environment body sourceFunction aliases labelVisibles)
      let visible ← Lifetimes.captureVisible
      return saveWith [.label (annotation.getD .actualLabel)] (label, .unit)
        (Loops.arguments visible) coreBody
  | .goto label => Scheduling.defer do
      let before ← Lifetimes.captureVisible
      let some after := LoopControl.lookup labelVisibles label
        | throw (.message "goto label has no collected lexical scope")
      return Lifetimes.transfer location label before after []
  | _ => Scheduling.defer (throw (.message "statement form is not ported by the actual elaborator"))
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem child.property
      omega

/-- Actual public statement translation keeps every source wrapper outside
execution of the staged raw node action. -/
def translate (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (statement : Ail.TypedStatement) (sourceFunction : Option Sym := none)
    (aliases : Designators.Aliases := []) (labelVisibles : LoopControl.Labels := []) : State.ElabM Effect :=
  annotate statement <$> Scheduling.execute
    (construct config types runtime environment statement sourceFunction aliases labelVisibles)

def translateList (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (statements : List Ail.TypedStatement) (sourceFunction : Option Sym := none)
    (aliases : Designators.Aliases := []) (labelVisibles : LoopControl.Labels := []) : State.ElabM (List Effect) :=
  Scheduling.execute (Scheduling.mapM (fun statement =>
    Scheduling.map (annotate statement)
      (construct config types runtime environment statement sourceFunction aliases labelVisibles)) statements)

end Silmaril.Cerberus.Elaboration.Statements
