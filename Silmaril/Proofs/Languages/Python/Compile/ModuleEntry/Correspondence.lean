module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry

theorem global_reference {scope : Source.Scope} {name : Source.Name}
    (reference : GlobalReference scope name) : globalReference? scope name = some reference := by
  obtain ⟨_, resolved, moduleName | declared⟩ := reference
  · subst moduleName
    simp [globalReference?, resolved]
  · subst declared
    simp [globalReference?, resolved]

theorem chain_iff (left : Int) (links : List (ScalarComparison × Int))
    (value : Bool) : ScalarComparison.chain left links = value ↔ ScalarComparison.EvaluatesChain left links value := by
  induction links generalizing left value with
  | nil =>
    constructor
    · intro result
      cases result
      exact .done left
    · intro result
      cases result
      rfl
  | cons link rest ih =>
    rcases link with ⟨operator, right⟩
    constructor
    · intro result
      cases passed : operator.test left right with
      | false =>
        simp [ScalarComparison.chain, passed] at result
        exact result ▸ .stop passed
      | true =>
        exact .next passed ((ih right value).mp (by simpa [ScalarComparison.chain, passed] using result))
    · intro result
      cases result with
      | stop failed => simp [ScalarComparison.chain, failed]
      | next passed tail => simpa [ScalarComparison.chain, passed] using (ih right value).mpr tail

theorem literalComparisonChain_iff (left : Source.Expr) (first second : Source.Comparison × Source.Expr)
    (rest : List (Source.Comparison × Source.Expr)) (result : Bool) :
    literalComparisonChain? left (first :: second :: rest) = some result ↔
      ∃ initial links, numericLiteral? left = some initial ∧
        (first :: second :: rest).mapM literalComparisonLink? = some links ∧
        ScalarComparison.EvaluatesChain initial links result := by
  cases initial : numericLiteral? left <;>
    cases links : (first :: second :: rest).mapM literalComparisonLink? <;>
    simp [literalComparisonChain?, initial, links, chain_iff]

theorem selectScalar_iff (operator : Source.BooleanOperator) (value : Core.Module.Value)
    (rest : List Core.Module.Value) (result : Core.Module.Value) :
    selectScalar operator value rest = result ↔ SelectsScalar operator value rest result := by
  induction rest generalizing value result with
  | nil =>
    constructor
    · intro same
      cases same
      exact .last value
    · intro selected
      cases selected
      rfl
  | cons next rest ih =>
    constructor
    · intro selected
      cases h : continuesSelection operator value with
      | false =>
        simp [selectScalar, h] at selected
        exact selected ▸ .stop h
      | true => exact .next h ((ih next result).mp (by simpa [selectScalar, h] using selected))
    · intro selected
      cases selected with
      | stop stopped => simp [selectScalar, stopped]
      | next continued tail => simpa [selectScalar, continued] using (ih next result).mpr tail

theorem literalBooleanOp_iff (operator : Source.BooleanOperator) (first second : Source.Expr)
    (rest : List Source.Expr) (result : Core.Module.Value) :
    literalBooleanOp? operator (first :: second :: rest) = some result ↔
      ∃ initial remaining, scalarLiteral? first = some initial ∧
        (second :: rest).mapM scalarLiteral? = some remaining ∧
        SelectsScalar operator initial remaining result := by
  cases initial : scalarLiteral? first <;>
    cases remaining : (second :: rest).mapM scalarLiteral? <;>
    simp [literalBooleanOp?, initial, remaining, selectScalar_iff]

theorem selectSourceScalar_iff (operator : Source.BooleanOperator) (value : Core.Module.Value)
    (rest : List Source.Expr) (result : Core.Module.Value) :
    selectSourceScalar? operator value rest = some result ↔ SelectsSourceScalar operator value rest result := by
  induction rest generalizing value result with
  | nil =>
    constructor
    · intro same
      cases same
      exact .last value
    · intro selected
      cases selected
      rfl
  | cons next rest ih =>
    constructor
    · intro selected
      cases continued : continuesSelection operator value with
      | false =>
        cases checked : (next :: rest).all skippedScalarSyntax with
        | false => simp [selectSourceScalar?, continued, checked] at selected
        | true =>
          have same : value = result := by simpa only [selectSourceScalar?, continued, Bool.false_eq_true,
            ↓reduceIte, checked, Option.some.injEq] using selected
          subst result
          exact .stop continued checked
      | true =>
        cases literal : scalarLiteral? next with
        | none => simp [selectSourceScalar?, continued, literal] at selected
        | some operand =>
          have tail : selectSourceScalar? operator operand rest = some result := by
            simpa [selectSourceScalar?, continued, literal] using selected
          exact .next continued literal ((ih operand result).mp tail)
    · intro selected
      cases selected with
      | stop decided checked => simp [selectSourceScalar?, decided, checked]
      | next continued literal tail => simp [selectSourceScalar?, continued, literal, (ih _ _).mpr tail]

theorem checkedBooleanOp_iff (operator : Source.BooleanOperator) (first second : Source.Expr)
    (rest : List Source.Expr) (result : Core.Module.Value) :
    checkedBooleanOp? operator (first :: second :: rest) = some result ↔
      ∃ initial, scalarLiteral? first = some initial ∧ SelectsSourceScalar operator initial (second :: rest) result := by
  cases initial : scalarLiteral? first <;> simp [checkedBooleanOp?, initial, selectSourceScalar_iff]

private theorem scalarLiteral_skippedSyntax (source : Source.Expr) {value : Core.Module.Value}
    (literal : scalarLiteral? source = some value) : skippedScalarSyntax source = true := by
  cases source with
  | unary op operand =>
    cases op <;> cases operand <;>
      simp_all [scalarLiteral?, integerLiteral?, skippedScalarSyntax]
  | integer | boolean => simp [skippedScalarSyntax]
  | _ => simp [scalarLiteral?, integerLiteral?] at literal

private theorem selectSourceScalar_closed (operator : Source.BooleanOperator) (source : List Source.Expr)
    (values : List Core.Module.Value) (closed : source.mapM scalarLiteral? = some values)
    (initial : Core.Module.Value) :
    source.all skippedScalarSyntax = true ∧
      selectSourceScalar? operator initial source = some (selectScalar operator initial values) := by
  induction source generalizing values initial with
  | nil =>
    cases closed
    exact ⟨rfl, rfl⟩
  | cons source rest ih =>
    cases head : scalarLiteral? source <;> cases tail : rest.mapM scalarLiteral? <;>
      simp [List.mapM_cons, head, tail] at closed
    subst values
    rename_i next remaining
    have tailChecked := ih remaining tail next
    have checked : (source :: rest).all skippedScalarSyntax = true := by
      simp [scalarLiteral_skippedSyntax _ head, tailChecked.1]
    refine ⟨checked, ?_⟩
    cases continued : continuesSelection operator initial with
    | true => simp [selectSourceScalar?, selectScalar, continued, head, tailChecked.2]
    | false => simp [selectSourceScalar?, selectScalar, continued, checked]

theorem checkedBooleanOp_closed (operator : Source.BooleanOperator) (operands : List Source.Expr)
    (value : Core.Module.Value) (closed : literalBooleanOp? operator operands = some value) :
    checkedBooleanOp? operator operands = some value := by
  match operands with
  | [] | [_] => contradiction
  | first :: second :: rest =>
    cases head : scalarLiteral? first <;> cases tail : (second :: rest).mapM scalarLiteral? <;>
      simp [literalBooleanOp?, head, tail] at closed
    subst value
    simpa [checkedBooleanOp?, head] using (selectSourceScalar_closed operator (second :: rest) _ tail _).2

theorem checkClosedSequence_complete {source : Source.Expr} {value : ClosedSequence}
    (checked : ClosedSequence.ValueOf source value) :
    checkClosedSequence source = some ⟨value, checked⟩ := by
  induction checked with
  | list checked | tuple checked =>
    rw [checkClosedSequence]
    split
    · rename_i missing
      cases checked.symm.trans missing
    · rename_i values found
      cases found.symm.trans checked
      rfl
  | append _ _ sameKind first second =>
    rw [checkClosedSequence, first, second]
    simp [bind, Option.bind, sameKind]

private theorem closedSequence_none {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) : checkClosedSequence source = none := by
  cases translated with
  | add left _ =>
    simp [checkClosedSequence, closedSequence_none left, bind, Option.bind]
  | _ => simp [checkClosedSequence]
termination_by sizeOf source

mutual
theorem operand_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) :
    lowerOperand scope source = .ok ⟨operand, translated⟩ := by
  cases translated with
  | integer => simp [lowerOperand]
  | boolean => simp [lowerOperand]
  | none_ => simp [lowerOperand]
  | negativeInteger => simp [lowerOperand]
  | literalDictionaryGet checked | literalDictionaryGetWith checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      cases Option.some.inj (computed.symm.trans checked)
      rfl
    · simp_all
  | literalSubscript selected =>
    rw [lowerOperand]
    split
    · rename_i value computed
      have equal := Option.some.inj (computed.symm.trans selected)
      subst value
      rfl
    · simp_all
  | read _ witness => simp [lowerOperand, global_reference witness]; rfl
  | add left right => simp [lowerOperand, operand_complete left, operand_complete right]; rfl
  | floorDiv left right => simp [lowerOperand, operand_complete left, operand_complete right]; rfl
  | @equal sourceLeft sourceRight _ _ left right =>
    have notFolded : closedSequenceComparison? sourceLeft .eq sourceRight = none := by
      simp [closedSequenceComparison?, closedSequence_none left]
    simp only [lowerOperand, identityOperator?]
    split
    · rename_i value folded
      cases folded.symm.trans notFolded
    · rw [operand_complete left, operand_complete right]
      rfl
  | @notEqual sourceLeft sourceRight _ _ left right =>
    have notFolded : closedSequenceComparison? sourceLeft .ne sourceRight = none := by
      simp [closedSequenceComparison?, closedSequence_none left]
    simp only [lowerOperand, identityOperator?]
    split
    · rename_i value folded
      cases folded.symm.trans notFolded
    · rw [operand_complete left, operand_complete right]
      rfl
  | @closedSequenceComparison left operator right value checked =>
    have ordinary : identityOperator? operator = none := by
      cases operator <;> first | rfl | simp [closedSequenceComparison?, literalTupleComparison?] at checked
    rw [lowerOperand]
    split
    · rename_i op recognized
      cases recognized.symm.trans ordinary
    · dsimp only
      split
      · rename_i decision computed
        cases computed.symm.trans checked
        rfl
      · rename_i absent
        cases checked.symm.trans absent
  | @literalComparisonChain left first second rest value checked =>
    obtain ⟨operator, right⟩ := first
    have ordinary : identityOperator? operator = none := by
      obtain ⟨_, _, _, admitted, _⟩ := (literalComparisonChain_iff left (operator, right) second rest value).mp checked
      cases operator <;> first | rfl | simp [literalComparisonLink?, ScalarComparison.ofSource?] at admitted
    rw [lowerOperand]
    split
    · rename_i op recognized
      cases recognized.symm.trans ordinary
    · dsimp only
      split
      · rename_i decision computed
        cases computed.symm.trans checked
        rfl
      · rename_i absent
        cases checked.symm.trans absent
  | literalNegation checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent
  | literalBooleanOp checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent
  | literalConditional guard yes no =>
    rw [lowerOperand]
    split
    · simp_all
    · rename_i decision chosen
      have equal := Option.some.inj (chosen.symm.trans guard)
      subst decision
      rw [operand_complete yes, operand_complete no]
      rfl
  | identityChain identified first singleton links =>
    rw [lowerOperand]
    split
    · rw [operand_complete first]
      simp only [bind, Except.bind, singleton, dite_true]
      rw [identityLinks_complete links]
      rfl
    · rename_i absent
      cases identified.symm.trans absent
termination_by sizeOf source

theorem identityLinks_complete {scope : Source.Scope} {source : List (Source.Comparison × Source.Expr)}
    {links : List (Core.Module.IdentityOperator × Operand scope)}
    (translated : IdentityLinksTranslation scope source links) :
    lowerIdentityLinks scope source = .ok ⟨links, translated⟩ := by
  cases translated with
  | done => simp [lowerIdentityLinks]
  | cons identified operand singleton tail =>
    rw [lowerIdentityLinks]
    split
    · rename_i absent
      cases identified.symm.trans absent
    · rename_i op checked
      cases checked.symm.trans identified
      rw [operand_complete operand]
      simp only [bind, Except.bind, singleton, dite_true]
      rw [identityLinks_complete tail]
      rfl
termination_by sizeOf source

end

theorem test_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : TestTranslation scope source operand) : lowerTest scope source = .ok ⟨operand, translated⟩ := by
  cases translated with
  | operand translated =>
    have absent : nonScalarLiteralTruth? source = none := by cases translated <;> rfl
    unfold lowerTest
    split
    · rename_i value checked
      cases checked.symm.trans absent
    · rw [operand_complete translated]
      rfl
  | literalTruth checked =>
    unfold lowerTest
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent

theorem statements_complete {scope : Source.Scope} {source : List Source.Stmt} {actions : List (Action scope)}
    (translated : Translation scope source actions) : lowerStatements scope source = .ok ⟨actions, translated⟩ := by
  induction translated with
  | done => simp [lowerStatements]
  | @assign statement name expression reference value rest next binding operand _ tail =>
    cases binding <;> (simp [lowerStatements, binding?, global_reference reference, operand_complete operand, tail]; rfl)
  | assertion operand _ tail => simp [lowerStatements, test_complete operand, tail]; rfl
  | globals _ tail => simp [lowerStatements, tail]
  | pass _ tail => simp [lowerStatements, tail]
  | literalIf arms guard _ _ _ yes no tail =>
    rw [lowerStatements, dite_eq_left arms]
    split
    · simp_all
    · rename_i decision chosen
      have equal := Option.some.inj (chosen.symm.trans guard)
      subst decision
      rw [yes, no, tail]
      rfl

theorem check_complete {source : Source.Module} {tree : Source.ScopeTree}
    {actions : List (Action tree.scope)} (analyzed : Source.analyze source = .ok tree)
    (moduleScope : tree.scope.context.kind = .module_) (translated : Translation tree.scope source.body actions) :
    check source = .ok ⟨tree, analyzed, moduleScope, actions, translated⟩ := by
  unfold check
  split
  · rename_i _ rejected
    rw [analyzed] at rejected
    contradiction
  · rename_i other accepted
    have same := Except.ok.inj (accepted.symm.trans analyzed)
    subst other
    simp [moduleScope, statements_complete translated]; rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry
