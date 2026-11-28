module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry

theorem ScalarComparison.chain_iff (left : Int) (links : List (ScalarComparison × Int))
    (value : Bool) : ScalarComparison.chain left links = value ↔ ScalarComparison.EvaluatesChain left links value :=
  Proofs.Languages.Python.Compile.ModuleEntry.chain_iff left links value

theorem literalComparisonChain_iff (left : Source.Expr) (first second : Source.Comparison × Source.Expr)
    (rest : List (Source.Comparison × Source.Expr)) (result : Bool) :
    literalComparisonChain? left (first :: second :: rest) = some result ↔
      ∃ initial links, numericLiteral? left = some initial ∧
        (first :: second :: rest).mapM literalComparisonLink? = some links ∧
        ScalarComparison.EvaluatesChain initial links result :=
  Proofs.Languages.Python.Compile.ModuleEntry.literalComparisonChain_iff left first second rest result

theorem selectScalar_iff (operator : Source.BooleanOperator) (value : Core.Module.Value)
    (rest : List Core.Module.Value) (result : Core.Module.Value) :
    selectScalar operator value rest = result ↔ SelectsScalar operator value rest result :=
  Proofs.Languages.Python.Compile.ModuleEntry.selectScalar_iff operator value rest result

theorem literalBooleanOp_iff (operator : Source.BooleanOperator) (first second : Source.Expr)
    (rest : List Source.Expr) (result : Core.Module.Value) :
    literalBooleanOp? operator (first :: second :: rest) = some result ↔
      ∃ initial remaining, scalarLiteral? first = some initial ∧
        (second :: rest).mapM scalarLiteral? = some remaining ∧
        SelectsScalar operator initial remaining result :=
  Proofs.Languages.Python.Compile.ModuleEntry.literalBooleanOp_iff operator first second rest result

theorem checkedBooleanOp_iff (operator : Source.BooleanOperator) (first second : Source.Expr)
    (rest : List Source.Expr) (result : Core.Module.Value) :
    checkedBooleanOp? operator (first :: second :: rest) = some result ↔
      ∃ initial, scalarLiteral? first = some initial ∧ SelectsSourceScalar operator initial (second :: rest) result :=
  Proofs.Languages.Python.Compile.ModuleEntry.checkedBooleanOp_iff operator first second rest result

theorem checkedBooleanOp_closed (operator : Source.BooleanOperator) (operands : List Source.Expr)
    (value : Core.Module.Value) (closed : literalBooleanOp? operator operands = some value) :
    checkedBooleanOp? operator operands = some value :=
  Proofs.Languages.Python.Compile.ModuleEntry.checkedBooleanOp_closed operator operands value closed

theorem test_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : TestTranslation scope source operand) : lowerTest scope source = .ok ⟨operand, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.test_complete translated

theorem global_reference {scope : Source.Scope} {name : Source.Name}
    (reference : GlobalReference scope name) : globalReference? scope name = some reference :=
  Proofs.Languages.Python.Compile.ModuleEntry.global_reference reference

theorem operand_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) :
    lowerOperand scope source = .ok ⟨operand, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.operand_complete translated

theorem checkClosedSequence_complete {source : Source.Expr} {value : ClosedSequence}
    (checked : ClosedSequence.ValueOf source value) :
    checkClosedSequence source = some ⟨value, checked⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.checkClosedSequence_complete checked

theorem lower_closedSequenceComparison {scope : Source.Scope} {left right : Source.Expr}
    {operator : Source.Comparison} {value : Bool}
    (checked : closedSequenceComparison? left operator right = some value) :
    lowerOperand scope (.comparison left [(operator, right)]) =
      .ok ⟨.booleanResult value, .closedSequenceComparison checked⟩ :=
  operand_complete (.closedSequenceComparison checked)

theorem lower_literalDictionaryGet {scope : Source.Scope} {entries : List (Option Source.Expr × Source.Expr)}
    {arguments : List Source.Expr} {value : Core.Module.Value}
    (checked : literalDictionaryGet? entries arguments = some value) :
    lowerOperand scope (.call (.attribute (.dictionary entries) "get") arguments) =
      .ok ⟨.scalarResult value, .literalDictionaryGet checked⟩ :=
  operand_complete (.literalDictionaryGet checked)

theorem lower_literalDictionaryGetWith {scope : Source.Scope} {entries : List (Option Source.Expr × Source.Expr)}
    {arguments : List (Source.ArgumentKind × Source.Expr)} {value : Core.Module.Value}
    (checked : literalDictionaryGetWith? entries arguments = some value) :
    lowerOperand scope (.callWith (.attribute (.dictionary entries) "get") arguments) =
      .ok ⟨.scalarResult value, .literalDictionaryGetWith checked⟩ :=
  operand_complete (.literalDictionaryGetWith checked)

theorem lower_checkedBooleanOp {scope : Source.Scope} {operator : Source.BooleanOperator}
    {operands : List Source.Expr} {value : Core.Module.Value}
    (checked : checkedBooleanOp? operator operands = some value) :
    lowerOperand scope (.booleanOp operator operands) = .ok ⟨.scalarResult value, .literalBooleanOp checked⟩ :=
  operand_complete (.literalBooleanOp checked)

theorem Operand.scalarResult_singletonResult {scope : Source.Scope} (value : Core.Module.Value) :
    (Operand.scalarResult (scope := scope) value).singletonResult = value.singleton?.isSome := by
  cases value <;> simp [Operand.scalarResult, Operand.singletonResult, Operand.comparable,
    Operand.booleanResult, Core.Module.Value.singleton?]

theorem statements_complete {scope : Source.Scope} {source : List Source.Stmt} {actions : List (Action scope)}
    (translated : Translation scope source actions) : lowerStatements scope source = .ok ⟨actions, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.statements_complete translated

theorem check_complete {source : Source.Module} {tree : Source.ScopeTree}
    {actions : List (Action tree.scope)} (analyzed : Source.analyze source = .ok tree)
    (moduleScope : tree.scope.context.kind = .module_) (translated : Translation tree.scope source.body actions) :
    check source = .ok ⟨tree, analyzed, moduleScope, actions, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.check_complete analyzed moduleScope translated

end Silmaril.Languages.Python.Compile.ModuleEntry
