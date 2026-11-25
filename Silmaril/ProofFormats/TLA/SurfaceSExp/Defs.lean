module

public import Silmaril.Formats.SExp.Dotted.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Defs

/-!
# TLA+ Surface S-expression codec

The version 1 schema is specified in `docs/projects/tla-surface-sexp.md`.
The public roots are compilation units and expressions. The codec validates
the wire shape and preserves unresolved Surface syntax.
-/

namespace Silmaril.ProofFormats.TLA.SurfaceSExp

open Silmaril.Formats
open Silmaril.Logic.Temporal.TLA.Surface

public abbrev Tree := DottedSExp.Datum

/-- Failures at the S-expression, envelope or Surface payload boundary. -/
public inductive DecodeError where
  /-- The input is not one complete S-expression, or the bytes are not UTF-8. -/
  | invalidSExpression
  /-- The schema identifier, version or envelope shape does not match. -/
  | invalidEnvelope
  /-- The payload does not have the requested root sort and field shapes. -/
  | invalidPayload
  /-- The candidate value re-encodes to a different tree. -/
  | noncanonical
  deriving DecidableEq, Repr

private def symbol (value : String) : Tree := .atom (.symbol value)
private def quoted (value : String) : Tree := .atom (.string value)

private def form (tag : String) (fields : List Tree) : Tree :=
  .cons (symbol tag) (SExp2.ofList fields)

private def writeName (value : Ident) : Tree := form "name" [quoted value]
private def writeNat (value : Nat) : Tree := symbol value.repr
private def writeBool : Bool → Tree
  | false => symbol "false"
  | true => symbol "true"

private def listForm : List Tree → Tree := form "list"

private def writeList {α : Type} (write : α → Tree) (items : List α) : Tree :=
  listForm (items.map write)

private def writeOption {α : Type} (write : α → Tree) : Option α → Tree
  | none => form "none" []
  | some value => form "some" [write value]

private def writeLiteral : Literal → Tree
  | .natural value => form "literal-natural" [writeNat value]
  | .decimal whole fractionalDigits =>
      form "literal-decimal" [writeNat whole, quoted fractionalDigits]
  | .string value => form "literal-string" [quoted value]

private def writePrefixOp : PrefixOp → Tree
  | .negation => form "prefix-op-negation" []
  | .minus => form "prefix-op-minus" []
  | .enabled => form "prefix-op-enabled" []
  | .unchanged => form "prefix-op-unchanged" []
  | .always => form "prefix-op-always" []
  | .eventually => form "prefix-op-eventually" []
  | .subset => form "prefix-op-subset" []
  | .union => form "prefix-op-union" []
  | .domain => form "prefix-op-domain" []
  | .symbol spelling => form "prefix-op-symbol" [quoted spelling]

private def writeInfixOp : InfixOp → Tree
  | .compose => form "infix-op-compose" []
  | .leadsTo => form "infix-op-leads-to" []
  | .guarantees => form "infix-op-guarantees" []
  | .symbol spelling => form "infix-op-symbol" [quoted spelling]

private def writePostfixOp : PostfixOp → Tree
  | .prime => form "postfix-op-prime" []
  | .symbol spelling => form "postfix-op-symbol" [quoted spelling]

private def writeSymbol : Symbol → Tree
  | .prefix op => form "symbol-prefix" [writePrefixOp op]
  | .infix op => form "symbol-infix" [writeInfixOp op]
  | .postfix op => form "symbol-postfix" [writePostfixOp op]

private def writeOperatorName : OperatorName → Tree
  | .ident name => form "operator-name-ident" [writeName name]
  | .symbolic op => form "operator-name-symbolic" [writeSymbol op]

private def writeOperatorDecl : OperatorDecl → Tree
  | .ident name arity => form "operator-decl-ident" [writeName name, writeNat arity]
  | .symbolic op => form "operator-decl-symbolic" [writeSymbol op]

private def writeOperatorHead : OperatorHead → Tree
  | .ident name parameters =>
      form "operator-head-ident" [writeName name, writeList writeOperatorDecl parameters]
  | .prefix op arg => form "operator-head-prefix" [writePrefixOp op, writeName arg]
  | .infix left op right =>
      form "operator-head-infix" [writeName left, writeInfixOp op, writeName right]
  | .postfix arg op => form "operator-head-postfix" [writeName arg, writePostfixOp op]

private def writeBoundPattern : BoundPattern → Tree
  | .ident name => form "bound-pattern-ident" [writeName name]
  | .tuple names => form "bound-pattern-tuple" [writeList writeName names]

private def writeBoundNames : BoundNames → Tree
  | .names names => form "bound-names-names" [writeList writeName names]
  | .tuple names => form "bound-names-tuple" [writeList writeName names]

private def writeQuantifier : Quantifier → Tree
  | .exists => form "quantifier-exists" []
  | .forall => form "quantifier-forall" []

private def writeJunction : Junction → Tree
  | .conjunction => form "junction-conjunction" []
  | .disjunction => form "junction-disjunction" []

private def writeActionBracket : ActionBracket → Tree
  | .square => form "action-bracket-square" []
  | .angle => form "action-bracket-angle" []

private def writeFairness : Fairness → Tree
  | .weak => form "fairness-weak" []
  | .strong => form "fairness-strong" []

private def writeStructuralSelector : StructuralSelector → Tree
  | .operand index => form "structural-selector-operand" [writeNat index]
  | .left => form "structural-selector-left" []
  | .right => form "structural-selector-right" []
  | .body => form "structural-selector-body" []
  | .allBindings => form "structural-selector-all-bindings" []

private def writeStepRefLevel : StepRefLevel → Tree
  | .explicit level => form "step-ref-level-explicit" [writeNat level]
  | .current => form "step-ref-level-current" []

private def writeStepRef : StepRef → Tree
  | .mk level name => form "step-ref" [writeStepRefLevel level, writeName name]

private def writeRefHead : RefHead → Tree
  | .operator name => form "ref-head-operator" [writeOperatorName name]
  | .step reference => form "ref-head-step" [writeStepRef reference]

private def writeLabel : Label → Tree
  | .mk name parameters => form "label" [writeName name, writeList writeName parameters]

private def writeVisibility : Visibility → Tree
  | .ordinary => form "visibility-ordinary" []
  | .local => form "visibility-local" []

mutual

private def writeExpr : Expr → Tree
  | .ref head args selectors =>
      form "expr-ref" [writeRefHead head, listForm (writeOpArgItems args),
        listForm (writeSelectorItems selectors)]
  | .literal value => form "expr-literal" [writeLiteral value]
  | .prefix op arg => form "expr-prefix" [writePrefixOp op, writeExpr arg]
  | .infix op left right => form "expr-infix" [writeInfixOp op, writeExpr left, writeExpr right]
  | .postfix op arg => form "expr-postfix" [writePostfixOp op, writeExpr arg]
  | .cartesian factors => form "expr-cartesian" [listForm (writeExprItems factors)]
  | .junction kind items =>
      form "expr-junction" [writeJunction kind, listForm (writeExprItems items)]
  | .ifThenElse condition consequent alternative =>
      form "expr-if-then-else" [writeExpr condition, writeExpr consequent, writeExpr alternative]
  | .cases arms other =>
      form "expr-cases" [listForm (writeCaseArmItems arms), writeExprOption other]
  | .letIn declarations body =>
      form "expr-let-in" [listForm (writeLetDeclItems declarations), writeExpr body]
  | .rigidQuant quantifier binders body =>
      form "expr-rigid-quant" [writeQuantifier quantifier, writeRigidBinders binders, writeExpr body]
  | .temporalQuant quantifier names body =>
      form "expr-temporal-quant" [writeQuantifier quantifier, writeList writeName names,
        writeExpr body]
  | .choose pattern domain predicate =>
      form "expr-choose" [writeBoundPattern pattern, writeExprOption domain, writeExpr predicate]
  | .setEnum elements => form "expr-set-enum" [listForm (writeExprItems elements)]
  | .setFilter pattern domain predicate =>
      form "expr-set-filter" [writeBoundPattern pattern, writeExpr domain, writeExpr predicate]
  | .setMap body bounds =>
      form "expr-set-map" [writeExpr body, listForm (writeBoundItems bounds)]
  | .function bounds body =>
      form "expr-function" [listForm (writeBoundItems bounds), writeExpr body]
  | .functionSet domain range => form "expr-function-set" [writeExpr domain, writeExpr range]
  | .index fn args => form "expr-index" [writeExpr fn, listForm (writeExprItems args)]
  | .tuple elements => form "expr-tuple" [listForm (writeExprItems elements)]
  | .record fields => form "expr-record" [listForm (writeFieldItems fields)]
  | .recordSet fields => form "expr-record-set" [listForm (writeFieldItems fields)]
  | .field record name => form "expr-field" [writeExpr record, writeName name]
  | .except base updates =>
      form "expr-except" [writeExpr base, listForm (writeUpdateItems updates)]
  | .oldValue => form "expr-old-value" []
  | .action kind body subscript =>
      form "expr-action" [writeActionBracket kind, writeExpr body, writeExpr subscript]
  | .fairness kind subscript action =>
      form "expr-fairness" [writeFairness kind, writeExpr subscript, writeExpr action]
  | .labeled label body => form "expr-labeled" [writeLabel label, writeExpr body]
termination_by structural value => value

private def writeOpArg : OpArg → Tree
  | .expr value => form "op-arg-expr" [writeExpr value]
  | .symbolic op => form "op-arg-symbolic" [writeSymbol op]
  | .lambda parameters body => form "op-arg-lambda" [writeList writeName parameters, writeExpr body]
termination_by structural value => value

private def writeSelector : Selector → Tree
  | .named name args =>
      form "selector-named" [writeOperatorName name, listForm (writeOpArgItems args)]
  | .arguments args => form "selector-arguments" [listForm (writeOpArgItems args)]
  | .structural selector => form "selector-structural" [writeStructuralSelector selector]
termination_by structural value => value

private def writeBound : Bound → Tree
  | .mk names domain => form "bound" [writeBoundNames names, writeExpr domain]
termination_by structural value => value

private def writeRigidBinders : RigidBinders → Tree
  | .unbounded names => form "rigid-binders-unbounded" [writeList writeName names]
  | .bounded groups => form "rigid-binders-bounded" [listForm (writeBoundItems groups)]
termination_by structural value => value

private def writeCaseArm : CaseArm → Tree
  | .mk condition result => form "case-arm" [writeExpr condition, writeExpr result]
termination_by structural value => value

private def writeField : Field → Tree
  | .mk name value => form "field" [writeName name, writeExpr value]
termination_by structural value => value

private def writeUpdateComponent : UpdateComponent → Tree
  | .field name => form "update-component-field" [writeName name]
  | .index args => form "update-component-index" [listForm (writeExprItems args)]
termination_by structural value => value

private def writeUpdate : Update → Tree
  | .mk path value =>
      form "update" [listForm (writeUpdateComponentItems path), writeExpr value]
termination_by structural value => value

private def writeSubstitution : Substitution → Tree
  | .mk target replacement =>
      form "substitution" [writeOperatorName target, writeOpArg replacement]
termination_by structural value => value

private def writeInstantiation : Instantiation → Tree
  | .mk moduleName substitutions =>
      form "instantiation" [writeName moduleName, listForm (writeSubstitutionItems substitutions)]
termination_by structural value => value

private def writeDefinition : Definition → Tree
  | .operator visibility head body =>
      form "definition-operator" [writeVisibility visibility, writeOperatorHead head, writeExpr body]
  | .function visibility name bounds body =>
      form "definition-function" [writeVisibility visibility, writeName name,
        listForm (writeBoundItems bounds), writeExpr body]
  | .namedInstance visibility name parameters instanceBody =>
      form "definition-named-instance" [writeVisibility visibility, writeName name,
        writeList writeOperatorDecl parameters, writeInstantiation instanceBody]
termination_by structural value => value

private def writeLetDecl : LetDecl → Tree
  | .definition value => form "let-decl-definition" [writeDefinition value]
  | .recursive operators => form "let-decl-recursive" [writeList writeOperatorDecl operators]
termination_by structural value => value

private def writeOpArgItems : List OpArg → List Tree
  | [] => []
  | item :: items => writeOpArg item :: writeOpArgItems items
termination_by structural items => items

private def writeSelectorItems : List Selector → List Tree
  | [] => []
  | item :: items => writeSelector item :: writeSelectorItems items
termination_by structural items => items

private def writeExprItems : List Expr → List Tree
  | [] => []
  | item :: items => writeExpr item :: writeExprItems items
termination_by structural items => items

private def writeCaseArmItems : List CaseArm → List Tree
  | [] => []
  | item :: items => writeCaseArm item :: writeCaseArmItems items
termination_by structural items => items

private def writeExprOption : Option Expr → Tree
  | none => form "none" []
  | some value => form "some" [writeExpr value]
termination_by structural value => value

private def writeLetDeclItems : List LetDecl → List Tree
  | [] => []
  | item :: items => writeLetDecl item :: writeLetDeclItems items
termination_by structural items => items

private def writeBoundItems : List Bound → List Tree
  | [] => []
  | item :: items => writeBound item :: writeBoundItems items
termination_by structural items => items

private def writeFieldItems : List Field → List Tree
  | [] => []
  | item :: items => writeField item :: writeFieldItems items
termination_by structural items => items

private def writeUpdateItems : List Update → List Tree
  | [] => []
  | item :: items => writeUpdate item :: writeUpdateItems items
termination_by structural items => items

private def writeUpdateComponentItems : List UpdateComponent → List Tree
  | [] => []
  | item :: items => writeUpdateComponent item :: writeUpdateComponentItems items
termination_by structural items => items

private def writeSubstitutionItems : List Substitution → List Tree
  | [] => []
  | item :: items => writeSubstitution item :: writeSubstitutionItems items
termination_by structural items => items

end

private def writeSymbolLevel : SymbolLevel → Tree
  | .constant => form "symbol-level-constant" []
  | .state => form "symbol-level-state" []
  | .action => form "symbol-level-action" []
  | .temporal => form "symbol-level-temporal" []

private def writeAssumeProveMode : AssumeProveMode → Tree
  | .plain => form "assume-prove-mode-plain" []
  | .boxed => form "assume-prove-mode-boxed" []

mutual

private def writeStatement : Statement → Tree
  | .expr value => form "statement-expr" [writeExpr value]
  | .assumeProve assumeMode hypotheses proveMode goal =>
      form "statement-assume-prove" [writeAssumeProveMode assumeMode, listForm (writeHypothesisItems hypotheses),
        writeAssumeProveMode proveMode, writeExpr goal]
  | .labeled name statement => form "statement-labeled" [writeName name, writeStatement statement]
termination_by structural value => value

private def writeHypothesis : Hypothesis → Tree
  | .statement value => form "hypothesis-statement" [writeStatement value]
  | .newSymbol level declaration =>
      form "hypothesis-new-symbol" [writeSymbolLevel level, writeOperatorDecl declaration]
  | .newVariable name => form "hypothesis-new-variable" [writeName name]
  | .newBoundConstant name domain =>
      form "hypothesis-new-bound-constant" [writeName name, writeExpr domain]
termination_by structural value => value

private def writeHypothesisItems : List Hypothesis → List Tree
  | [] => []
  | item :: items => writeHypothesis item :: writeHypothesisItems items
termination_by structural items => items

end

private def writeCitation : Citation → Tree
  | .expr value => form "citation-expr" [writeExpr value]
  | .moduleName name => form "citation-module-name" [writeName name]

private def writeCitations : Citations → Tree
  | .mk facts defs =>
      form "citations" [writeList writeCitation facts, writeList writeCitation defs]

private def writeDirective : Directive → Tree
  | .use only citations => form "directive-use" [writeBool only, writeCitations citations]
  | .hide citations => form "directive-hide" [writeCitations citations]

private def writeStepLevel : StepLevel → Tree
  | .explicit level => form "step-level-explicit" [writeNat level]
  | .current => form "step-level-current" []
  | .next => form "step-level-next" []

private def writeStepLabel : StepLabel → Tree
  | .mk level name => form "step-label" [writeStepLevel level, writeOption writeName name]

mutual

private def writeProof : Proof → Tree
  | .obvious => form "proof-obvious" []
  | .omitted => form "proof-omitted" []
  | .byFacts only citations => form "proof-by-facts" [writeBool only, writeCitations citations]
  | .steps steps qedLabel qedProof =>
      form "proof-steps" [listForm (writeProofStepItems steps), writeStepLabel qedLabel,
        writeProofOption qedProof]
termination_by structural value => value

private def writeProofStep : ProofStep → Tree
  | .mk label body => form "proof-step" [writeStepLabel label, writeStepBody body]
termination_by structural value => value

private def writeStepBody : StepBody → Tree
  | .directive value => form "step-body-directive" [writeDirective value]
  | .instantiation value => form "step-body-instantiation" [writeInstantiation value]
  | .define definitions => form "step-body-define" [writeList writeDefinition definitions]
  | .have value => form "step-body-have" [writeExpr value]
  | .take binders => form "step-body-take" [writeRigidBinders binders]
  | .witness values => form "step-body-witness" [writeList writeExpr values]
  | .pick binders predicate proof =>
      form "step-body-pick" [writeRigidBinders binders, writeExpr predicate, writeProofOption proof]
  | .caseOf condition proof =>
      form "step-body-case-of" [writeExpr condition, writeProofOption proof]
  | .assert statement proof =>
      form "step-body-assert" [writeStatement statement, writeProofOption proof]
  | .suffices statement proof =>
      form "step-body-suffices" [writeStatement statement, writeProofOption proof]
termination_by structural value => value

private def writeProofStepItems : List ProofStep → List Tree
  | [] => []
  | item :: items => writeProofStep item :: writeProofStepItems items
termination_by structural items => items

private def writeProofOption : Option Proof → Tree
  | none => form "none" []
  | some value => form "some" [writeProof value]
termination_by structural value => value

end

private def writeTheorem : Theorem → Tree
  | .mk name statement proof =>
      form "theorem" [writeOption writeName name, writeStatement statement,
        writeOption writeProof proof]

mutual

private def writeModule : Module → Tree
  | .mk name extendsModules units =>
      form "module" [writeName name, writeList writeName extendsModules,
        listForm (writeModuleUnitItems units)]
termination_by structural value => value

private def writeModuleUnit : ModuleUnit → Tree
  | .variables names => form "module-unit-variables" [writeList writeName names]
  | .constants operators => form "module-unit-constants" [writeList writeOperatorDecl operators]
  | .recursive operators => form "module-unit-recursive" [writeList writeOperatorDecl operators]
  | .definition value => form "module-unit-definition" [writeDefinition value]
  | .instantiation visibility value =>
      form "module-unit-instantiation" [writeVisibility visibility, writeInstantiation value]
  | .assumption name body =>
      form "module-unit-assumption" [writeOption writeName name, writeExpr body]
  | .theoremDecl value => form "module-unit-theorem-decl" [writeTheorem value]
  | .submodule value => form "module-unit-submodule" [writeModule value]
  | .directive value => form "module-unit-directive" [writeDirective value]
termination_by structural value => value

private def writeModuleUnitItems : List ModuleUnit → List Tree
  | [] => []
  | item :: items => writeModuleUnit item :: writeModuleUnitItems items
termination_by structural items => items

end

-- The fold retains the child readers of each proper cons spine. A child reader
-- can only run the constructor at its own tag and requested AST sort.
private inductive Kind : Type → Type where
  | kLiteral : Kind Literal
  | kPrefixOp : Kind PrefixOp
  | kInfixOp : Kind InfixOp
  | kPostfixOp : Kind PostfixOp
  | kSymbol : Kind Symbol
  | kOperatorName : Kind OperatorName
  | kOperatorDecl : Kind OperatorDecl
  | kOperatorHead : Kind OperatorHead
  | kBoundPattern : Kind BoundPattern
  | kBoundNames : Kind BoundNames
  | kQuantifier : Kind Quantifier
  | kJunction : Kind Junction
  | kActionBracket : Kind ActionBracket
  | kFairness : Kind Fairness
  | kStructuralSelector : Kind StructuralSelector
  | kStepRefLevel : Kind StepRefLevel
  | kStepRef : Kind StepRef
  | kRefHead : Kind RefHead
  | kLabel : Kind Label
  | kVisibility : Kind Visibility
  | kExpr : Kind Expr
  | kOpArg : Kind OpArg
  | kSelector : Kind Selector
  | kBound : Kind Bound
  | kRigidBinders : Kind RigidBinders
  | kCaseArm : Kind CaseArm
  | kField : Kind Field
  | kUpdateComponent : Kind UpdateComponent
  | kUpdate : Kind Update
  | kSubstitution : Kind Substitution
  | kInstantiation : Kind Instantiation
  | kDefinition : Kind Definition
  | kLetDecl : Kind LetDecl
  | kSymbolLevel : Kind SymbolLevel
  | kAssumeProveMode : Kind AssumeProveMode
  | kStatement : Kind Statement
  | kHypothesis : Kind Hypothesis
  | kCitation : Kind Citation
  | kCitations : Kind Citations
  | kDirective : Kind Directive
  | kStepLevel : Kind StepLevel
  | kStepLabel : Kind StepLabel
  | kProof : Kind Proof
  | kProofStep : Kind ProofStep
  | kStepBody : Kind StepBody
  | kTheorem : Kind Theorem
  | kModule : Kind Module
  | kModuleUnit : Kind ModuleUnit

private inductive Checked where
  | atom (value : DottedSExp.Atom)
  | name (value : Ident)
  | list (items : List Checked)
  | absent
  | present (value : Checked)
  | constructor (read : {α : Type} → Kind α → Option α)
  | malformed

private def readKind {α : Type} (kind : Kind α) : Checked → Option α
  | .constructor decode => decode kind
  | _ => none

private def readName : Checked → Option Ident
  | .name value => some value
  | _ => none

private def readText : Checked → Option String
  | .atom (.string value) => some value
  | _ => none

-- The public re-encoding check also rejects noncanonical spellings, including
-- leading zeroes in a numeric atom.
private def readNat : Checked → Option Nat
  | .atom (.symbol value) => value.toNat?
  | _ => none

private def readBool : Checked → Option Bool
  | .atom (.symbol "false") => some false
  | .atom (.symbol "true") => some true
  | _ => none

private def readList {α : Type} (parse : Checked → Option α) : Checked → Option (List α)
  | .list items => items.mapM parse
  | _ => none

private def readOption {α : Type} (parse : Checked → Option α) : Checked → Option (Option α)
  | .absent => some none
  | .present value => some <$> parse value
  | _ => none

private def readLiteralFields : String → List Checked → Option Literal
  | "literal-natural", [value] => return .natural (← readNat value)
  | "literal-decimal", [whole, fractionalDigits] => do
      return .decimal (← readNat whole) (← readText fractionalDigits)
  | "literal-string", [value] => return .string (← readText value)
  | _, _ => none

private def readPrefixOpFields : String → List Checked → Option PrefixOp
  | "prefix-op-negation", [] => some .negation
  | "prefix-op-minus", [] => some .minus
  | "prefix-op-enabled", [] => some .enabled
  | "prefix-op-unchanged", [] => some .unchanged
  | "prefix-op-always", [] => some .always
  | "prefix-op-eventually", [] => some .eventually
  | "prefix-op-subset", [] => some .subset
  | "prefix-op-union", [] => some .union
  | "prefix-op-domain", [] => some .domain
  | "prefix-op-symbol", [spelling] => return .symbol (← readText spelling)
  | _, _ => none

private def readInfixOpFields : String → List Checked → Option InfixOp
  | "infix-op-compose", [] => some .compose
  | "infix-op-leads-to", [] => some .leadsTo
  | "infix-op-guarantees", [] => some .guarantees
  | "infix-op-symbol", [spelling] => return .symbol (← readText spelling)
  | _, _ => none

private def readPostfixOpFields : String → List Checked → Option PostfixOp
  | "postfix-op-prime", [] => some .prime
  | "postfix-op-symbol", [spelling] => return .symbol (← readText spelling)
  | _, _ => none

private def readSymbolFields : String → List Checked → Option Symbol
  | "symbol-prefix", [op] => return .prefix (← readKind .kPrefixOp op)
  | "symbol-infix", [op] => return .infix (← readKind .kInfixOp op)
  | "symbol-postfix", [op] => return .postfix (← readKind .kPostfixOp op)
  | _, _ => none

private def readOperatorNameFields : String → List Checked → Option OperatorName
  | "operator-name-ident", [name] => return .ident (← readName name)
  | "operator-name-symbolic", [op] => return .symbolic (← readKind .kSymbol op)
  | _, _ => none

private def readOperatorDeclFields : String → List Checked → Option OperatorDecl
  | "operator-decl-ident", [name, arity] => return .ident (← readName name) (← readNat arity)
  | "operator-decl-symbolic", [op] => return .symbolic (← readKind .kSymbol op)
  | _, _ => none

private def readOperatorHeadFields : String → List Checked → Option OperatorHead
  | "operator-head-ident", [name, parameters] => do
      return .ident (← readName name) (← readList (readKind .kOperatorDecl) parameters)
  | "operator-head-prefix", [op, arg] => return .prefix (← readKind .kPrefixOp op) (← readName arg)
  | "operator-head-infix", [left, op, right] => do
      return .infix (← readName left) (← readKind .kInfixOp op) (← readName right)
  | "operator-head-postfix", [arg, op] => do
      return .postfix (← readName arg) (← readKind .kPostfixOp op)
  | _, _ => none

private def readBoundPatternFields : String → List Checked → Option BoundPattern
  | "bound-pattern-ident", [name] => return .ident (← readName name)
  | "bound-pattern-tuple", [names] => return .tuple (← readList readName names)
  | _, _ => none

private def readBoundNamesFields : String → List Checked → Option BoundNames
  | "bound-names-names", [names] => return .names (← readList readName names)
  | "bound-names-tuple", [names] => return .tuple (← readList readName names)
  | _, _ => none

private def readQuantifierFields : String → List Checked → Option Quantifier
  | "quantifier-exists", [] => some .exists
  | "quantifier-forall", [] => some .forall
  | _, _ => none

private def readJunctionFields : String → List Checked → Option Junction
  | "junction-conjunction", [] => some .conjunction
  | "junction-disjunction", [] => some .disjunction
  | _, _ => none

private def readActionBracketFields : String → List Checked → Option ActionBracket
  | "action-bracket-square", [] => some .square
  | "action-bracket-angle", [] => some .angle
  | _, _ => none

private def readFairnessFields : String → List Checked → Option Fairness
  | "fairness-weak", [] => some .weak
  | "fairness-strong", [] => some .strong
  | _, _ => none

private def readStructuralSelectorFields : String → List Checked → Option StructuralSelector
  | "structural-selector-operand", [index] => return .operand (← readNat index)
  | "structural-selector-left", [] => some .left
  | "structural-selector-right", [] => some .right
  | "structural-selector-body", [] => some .body
  | "structural-selector-all-bindings", [] => some .allBindings
  | _, _ => none

private def readStepRefLevelFields : String → List Checked → Option StepRefLevel
  | "step-ref-level-explicit", [level] => return .explicit (← readNat level)
  | "step-ref-level-current", [] => some .current
  | _, _ => none

private def readStepRefFields : String → List Checked → Option StepRef
  | "step-ref", [level, name] => return .mk (← readKind .kStepRefLevel level) (← readName name)
  | _, _ => none

private def readRefHeadFields : String → List Checked → Option RefHead
  | "ref-head-operator", [name] => return .operator (← readKind .kOperatorName name)
  | "ref-head-step", [reference] => return .step (← readKind .kStepRef reference)
  | _, _ => none

private def readLabelFields : String → List Checked → Option Label
  | "label", [name, parameters] => return .mk (← readName name) (← readList readName parameters)
  | _, _ => none

private def readVisibilityFields : String → List Checked → Option Visibility
  | "visibility-ordinary", [] => some .ordinary
  | "visibility-local", [] => some .local
  | _, _ => none

private def readExprFields : String → List Checked → Option Expr
  | "expr-ref", [head, args, selectors] => do
      return .ref (← readKind .kRefHead head) (← readList (readKind .kOpArg) args)
        (← readList (readKind .kSelector) selectors)
  | "expr-literal", [value] => return .literal (← readKind .kLiteral value)
  | "expr-prefix", [op, arg] => return .prefix (← readKind .kPrefixOp op) (← readKind .kExpr arg)
  | "expr-infix", [op, left, right] => do
      return .infix (← readKind .kInfixOp op) (← readKind .kExpr left) (← readKind .kExpr right)
  | "expr-postfix", [op, arg] => return .postfix (← readKind .kPostfixOp op) (← readKind .kExpr arg)
  | "expr-cartesian", [factors] => return .cartesian (← readList (readKind .kExpr) factors)
  | "expr-junction", [kind, items] => do
      return .junction (← readKind .kJunction kind) (← readList (readKind .kExpr) items)
  | "expr-if-then-else", [condition, consequent, alternative] => do
      return .ifThenElse (← readKind .kExpr condition) (← readKind .kExpr consequent)
        (← readKind .kExpr alternative)
  | "expr-cases", [arms, other] => do
      return .cases (← readList (readKind .kCaseArm) arms) (← readOption (readKind .kExpr) other)
  | "expr-let-in", [declarations, body] => do
      return .letIn (← readList (readKind .kLetDecl) declarations) (← readKind .kExpr body)
  | "expr-rigid-quant", [quantifier, binders, body] => do
      return .rigidQuant (← readKind .kQuantifier quantifier) (← readKind .kRigidBinders binders)
        (← readKind .kExpr body)
  | "expr-temporal-quant", [quantifier, names, body] => do
      return .temporalQuant (← readKind .kQuantifier quantifier) (← readList readName names)
        (← readKind .kExpr body)
  | "expr-choose", [pattern, domain, predicate] => do
      return .choose (← readKind .kBoundPattern pattern) (← readOption (readKind .kExpr) domain)
        (← readKind .kExpr predicate)
  | "expr-set-enum", [elements] => return .setEnum (← readList (readKind .kExpr) elements)
  | "expr-set-filter", [pattern, domain, predicate] => do
      return .setFilter (← readKind .kBoundPattern pattern) (← readKind .kExpr domain)
        (← readKind .kExpr predicate)
  | "expr-set-map", [body, bounds] => do
      return .setMap (← readKind .kExpr body) (← readList (readKind .kBound) bounds)
  | "expr-function", [bounds, body] => do
      return .function (← readList (readKind .kBound) bounds) (← readKind .kExpr body)
  | "expr-function-set", [domain, range] => do
      return .functionSet (← readKind .kExpr domain) (← readKind .kExpr range)
  | "expr-index", [fn, args] => do
      return .index (← readKind .kExpr fn) (← readList (readKind .kExpr) args)
  | "expr-tuple", [elements] => return .tuple (← readList (readKind .kExpr) elements)
  | "expr-record", [fields] => return .record (← readList (readKind .kField) fields)
  | "expr-record-set", [fields] => return .recordSet (← readList (readKind .kField) fields)
  | "expr-field", [record, name] => return .field (← readKind .kExpr record) (← readName name)
  | "expr-except", [base, updates] => do
      return .except (← readKind .kExpr base) (← readList (readKind .kUpdate) updates)
  | "expr-old-value", [] => some .oldValue
  | "expr-action", [kind, body, subscript] => do
      return .action (← readKind .kActionBracket kind) (← readKind .kExpr body)
        (← readKind .kExpr subscript)
  | "expr-fairness", [kind, subscript, action] => do
      return .fairness (← readKind .kFairness kind) (← readKind .kExpr subscript)
        (← readKind .kExpr action)
  | "expr-labeled", [label, body] => do
      return .labeled (← readKind .kLabel label) (← readKind .kExpr body)
  | _, _ => none

private def readOpArgFields : String → List Checked → Option OpArg
  | "op-arg-expr", [value] => return .expr (← readKind .kExpr value)
  | "op-arg-symbolic", [op] => return .symbolic (← readKind .kSymbol op)
  | "op-arg-lambda", [parameters, body] => do
      return .lambda (← readList readName parameters) (← readKind .kExpr body)
  | _, _ => none

private def readSelectorFields : String → List Checked → Option Selector
  | "selector-named", [name, args] => do
      return .named (← readKind .kOperatorName name) (← readList (readKind .kOpArg) args)
  | "selector-arguments", [args] => return .arguments (← readList (readKind .kOpArg) args)
  | "selector-structural", [selector] => do
      return .structural (← readKind .kStructuralSelector selector)
  | _, _ => none

private def readBoundFields : String → List Checked → Option Bound
  | "bound", [names, domain] => return .mk (← readKind .kBoundNames names) (← readKind .kExpr domain)
  | _, _ => none

private def readRigidBindersFields : String → List Checked → Option RigidBinders
  | "rigid-binders-unbounded", [names] => return .unbounded (← readList readName names)
  | "rigid-binders-bounded", [groups] => return .bounded (← readList (readKind .kBound) groups)
  | _, _ => none

private def readCaseArmFields : String → List Checked → Option CaseArm
  | "case-arm", [condition, result] => do
      return .mk (← readKind .kExpr condition) (← readKind .kExpr result)
  | _, _ => none

private def readFieldFields : String → List Checked → Option Field
  | "field", [name, value] => return .mk (← readName name) (← readKind .kExpr value)
  | _, _ => none

private def readUpdateComponentFields : String → List Checked → Option UpdateComponent
  | "update-component-field", [name] => return .field (← readName name)
  | "update-component-index", [args] => return .index (← readList (readKind .kExpr) args)
  | _, _ => none

private def readUpdateFields : String → List Checked → Option Update
  | "update", [path, value] => do
      return .mk (← readList (readKind .kUpdateComponent) path) (← readKind .kExpr value)
  | _, _ => none

private def readSubstitutionFields : String → List Checked → Option Substitution
  | "substitution", [target, replacement] => do
      return .mk (← readKind .kOperatorName target) (← readKind .kOpArg replacement)
  | _, _ => none

private def readInstantiationFields : String → List Checked → Option Instantiation
  | "instantiation", [moduleName, substitutions] => do
      return .mk (← readName moduleName) (← readList (readKind .kSubstitution) substitutions)
  | _, _ => none

private def readDefinitionFields : String → List Checked → Option Definition
  | "definition-operator", [visibility, head, body] => do
      return .operator (← readKind .kVisibility visibility) (← readKind .kOperatorHead head)
        (← readKind .kExpr body)
  | "definition-function", [visibility, name, bounds, body] => do
      return .function (← readKind .kVisibility visibility) (← readName name)
        (← readList (readKind .kBound) bounds) (← readKind .kExpr body)
  | "definition-named-instance", [visibility, name, parameters, instanceBody] => do
      return .namedInstance (← readKind .kVisibility visibility) (← readName name)
        (← readList (readKind .kOperatorDecl) parameters) (← readKind .kInstantiation instanceBody)
  | _, _ => none

private def readLetDeclFields : String → List Checked → Option LetDecl
  | "let-decl-definition", [value] => return .definition (← readKind .kDefinition value)
  | "let-decl-recursive", [operators] => do
      return .recursive (← readList (readKind .kOperatorDecl) operators)
  | _, _ => none

private def readSymbolLevelFields : String → List Checked → Option SymbolLevel
  | "symbol-level-constant", [] => some .constant
  | "symbol-level-state", [] => some .state
  | "symbol-level-action", [] => some .action
  | "symbol-level-temporal", [] => some .temporal
  | _, _ => none

private def readAssumeProveModeFields : String → List Checked → Option AssumeProveMode
  | "assume-prove-mode-plain", [] => some .plain
  | "assume-prove-mode-boxed", [] => some .boxed
  | _, _ => none

private def readStatementFields : String → List Checked → Option Statement
  | "statement-expr", [value] => return .expr (← readKind .kExpr value)
  | "statement-assume-prove", [assumeMode, hypotheses, proveMode, goal] => do
      return .assumeProve (← readKind .kAssumeProveMode assumeMode)
        (← readList (readKind .kHypothesis) hypotheses) (← readKind .kAssumeProveMode proveMode)
        (← readKind .kExpr goal)
  | "statement-labeled", [name, statement] => do
      return .labeled (← readName name) (← readKind .kStatement statement)
  | _, _ => none

private def readHypothesisFields : String → List Checked → Option Hypothesis
  | "hypothesis-statement", [value] => return .statement (← readKind .kStatement value)
  | "hypothesis-new-symbol", [level, declaration] => do
      return .newSymbol (← readKind .kSymbolLevel level) (← readKind .kOperatorDecl declaration)
  | "hypothesis-new-variable", [name] => return .newVariable (← readName name)
  | "hypothesis-new-bound-constant", [name, domain] => do
      return .newBoundConstant (← readName name) (← readKind .kExpr domain)
  | _, _ => none

private def readCitationFields : String → List Checked → Option Citation
  | "citation-expr", [value] => return .expr (← readKind .kExpr value)
  | "citation-module-name", [name] => return .moduleName (← readName name)
  | _, _ => none

private def readCitationsFields : String → List Checked → Option Citations
  | "citations", [facts, defs] => do
      return .mk (← readList (readKind .kCitation) facts) (← readList (readKind .kCitation) defs)
  | _, _ => none

private def readDirectiveFields : String → List Checked → Option Directive
  | "directive-use", [only, citations] => do
      return .use (← readBool only) (← readKind .kCitations citations)
  | "directive-hide", [citations] => return .hide (← readKind .kCitations citations)
  | _, _ => none

private def readStepLevelFields : String → List Checked → Option StepLevel
  | "step-level-explicit", [level] => return .explicit (← readNat level)
  | "step-level-current", [] => some .current
  | "step-level-next", [] => some .next
  | _, _ => none

private def readStepLabelFields : String → List Checked → Option StepLabel
  | "step-label", [level, name] => do
      return .mk (← readKind .kStepLevel level) (← readOption readName name)
  | _, _ => none

private def readProofFields : String → List Checked → Option Proof
  | "proof-obvious", [] => some .obvious
  | "proof-omitted", [] => some .omitted
  | "proof-by-facts", [only, citations] => do
      return .byFacts (← readBool only) (← readKind .kCitations citations)
  | "proof-steps", [steps, qedLabel, qedProof] => do
      return .steps (← readList (readKind .kProofStep) steps) (← readKind .kStepLabel qedLabel)
        (← readOption (readKind .kProof) qedProof)
  | _, _ => none

private def readProofStepFields : String → List Checked → Option ProofStep
  | "proof-step", [label, body] => do
      return .mk (← readKind .kStepLabel label) (← readKind .kStepBody body)
  | _, _ => none

private def readStepBodyFields : String → List Checked → Option StepBody
  | "step-body-directive", [value] => return .directive (← readKind .kDirective value)
  | "step-body-instantiation", [value] => return .instantiation (← readKind .kInstantiation value)
  | "step-body-define", [definitions] => do
      return .define (← readList (readKind .kDefinition) definitions)
  | "step-body-have", [value] => return .have (← readKind .kExpr value)
  | "step-body-take", [binders] => return .take (← readKind .kRigidBinders binders)
  | "step-body-witness", [values] => return .witness (← readList (readKind .kExpr) values)
  | "step-body-pick", [binders, predicate, proof] => do
      return .pick (← readKind .kRigidBinders binders) (← readKind .kExpr predicate)
        (← readOption (readKind .kProof) proof)
  | "step-body-case-of", [condition, proof] => do
      return .caseOf (← readKind .kExpr condition) (← readOption (readKind .kProof) proof)
  | "step-body-assert", [statement, proof] => do
      return .assert (← readKind .kStatement statement) (← readOption (readKind .kProof) proof)
  | "step-body-suffices", [statement, proof] => do
      return .suffices (← readKind .kStatement statement) (← readOption (readKind .kProof) proof)
  | _, _ => none

private def readTheoremFields : String → List Checked → Option Theorem
  | "theorem", [name, statement, proof] => do
      return .mk (← readOption readName name) (← readKind .kStatement statement)
        (← readOption (readKind .kProof) proof)
  | _, _ => none

private def readModuleFields : String → List Checked → Option Module
  | "module", [name, extendsModules, units] => do
      return .mk (← readName name) (← readList readName extendsModules)
        (← readList (readKind .kModuleUnit) units)
  | _, _ => none

private def readModuleUnitFields : String → List Checked → Option ModuleUnit
  | "module-unit-variables", [names] => return .variables (← readList readName names)
  | "module-unit-constants", [operators] => do
      return .constants (← readList (readKind .kOperatorDecl) operators)
  | "module-unit-recursive", [operators] => do
      return .recursive (← readList (readKind .kOperatorDecl) operators)
  | "module-unit-definition", [value] => return .definition (← readKind .kDefinition value)
  | "module-unit-instantiation", [visibility, value] => do
      return .instantiation (← readKind .kVisibility visibility) (← readKind .kInstantiation value)
  | "module-unit-assumption", [name, body] => do
      return .assumption (← readOption readName name) (← readKind .kExpr body)
  | "module-unit-theorem-decl", [value] => return .theoremDecl (← readKind .kTheorem value)
  | "module-unit-submodule", [value] => return .submodule (← readKind .kModule value)
  | "module-unit-directive", [value] => return .directive (← readKind .kDirective value)
  | _, _ => none

private def readFields {α : Type} : Kind α → String → List Checked → Option α
  | .kLiteral => readLiteralFields
  | .kPrefixOp => readPrefixOpFields
  | .kInfixOp => readInfixOpFields
  | .kPostfixOp => readPostfixOpFields
  | .kSymbol => readSymbolFields
  | .kOperatorName => readOperatorNameFields
  | .kOperatorDecl => readOperatorDeclFields
  | .kOperatorHead => readOperatorHeadFields
  | .kBoundPattern => readBoundPatternFields
  | .kBoundNames => readBoundNamesFields
  | .kQuantifier => readQuantifierFields
  | .kJunction => readJunctionFields
  | .kActionBracket => readActionBracketFields
  | .kFairness => readFairnessFields
  | .kStructuralSelector => readStructuralSelectorFields
  | .kStepRefLevel => readStepRefLevelFields
  | .kStepRef => readStepRefFields
  | .kRefHead => readRefHeadFields
  | .kLabel => readLabelFields
  | .kVisibility => readVisibilityFields
  | .kExpr => readExprFields
  | .kOpArg => readOpArgFields
  | .kSelector => readSelectorFields
  | .kBound => readBoundFields
  | .kRigidBinders => readRigidBindersFields
  | .kCaseArm => readCaseArmFields
  | .kField => readFieldFields
  | .kUpdateComponent => readUpdateComponentFields
  | .kUpdate => readUpdateFields
  | .kSubstitution => readSubstitutionFields
  | .kInstantiation => readInstantiationFields
  | .kDefinition => readDefinitionFields
  | .kLetDecl => readLetDeclFields
  | .kSymbolLevel => readSymbolLevelFields
  | .kAssumeProveMode => readAssumeProveModeFields
  | .kStatement => readStatementFields
  | .kHypothesis => readHypothesisFields
  | .kCitation => readCitationFields
  | .kCitations => readCitationsFields
  | .kDirective => readDirectiveFields
  | .kStepLevel => readStepLevelFields
  | .kStepLabel => readStepLabelFields
  | .kProof => readProofFields
  | .kProofStep => readProofStepFields
  | .kStepBody => readStepBodyFields
  | .kTheorem => readTheoremFields
  | .kModule => readModuleFields
  | .kModuleUnit => readModuleUnitFields

private def checkForm : List Checked → Checked
  | .atom (.symbol "list") :: items => .list items
  | [.atom (.symbol "none")] => .absent
  | [.atom (.symbol "some"), value] => .present value
  | [.atom (.symbol "name"), .atom (.string value)] => .name value
  | .atom (.symbol tag) :: fields => .constructor (fun kind => readFields kind tag fields)
  | _ => .malformed

/-- Fold the binary tree. The second projection is present exactly on
nil-terminated spines, and the first interprets the whole node as a field. -/
private def check : Tree → Checked × Option (List Checked)
  | .nil => (.malformed, some [])
  | .atom value => (.atom value, none)
  | .cons head tail =>
    match (check tail).2 with
    | none => (.malformed, none)
    | some rest =>
      let items := (check head).1 :: rest
      (checkForm items, some items)

private def envelope (payload : Tree) : Tree :=
  form "tla-surface" [symbol "1", payload]

private def payload? : Tree → Option Tree
  | .cons (.atom (.symbol "tla-surface")) (.cons (.atom (.symbol "1")) (.cons payload .nil)) =>
    some payload
  | _ => none

private def decodeRoot {α : Type} (kind : Kind α) (encode : α → Tree) (tree : Tree) :
    Except DecodeError α := do
  let some payload := payload? tree | .error .invalidEnvelope
  let some value := readKind kind (check payload).1 | .error .invalidPayload
  if encode value = tree then .ok value else .error .noncanonical

private def decodeWire {α β : Type} (parse : α → Option Tree)
    (decode : Tree → Except DecodeError β) (input : α) : Except DecodeError β :=
  match parse input with
  | some tree => decode tree
  | none => .error .invalidSExpression

/-- Encode a complete Surface module in the version 1 envelope. -/
public def encodeModule (value : Module) : Tree := envelope (writeModule value)

/-- Decode exactly one versioned module tree. -/
public def decodeModule : Tree → Except DecodeError Module := decodeRoot .kModule encodeModule

/-- Encode a standalone Surface expression in the version 1 envelope. -/
public def encodeExpr (value : Expr) : Tree := envelope (writeExpr value)

/-- Decode exactly one versioned expression tree. -/
public def decodeExpr : Tree → Except DecodeError Expr := decodeRoot .kExpr encodeExpr

public def encodeModuleText (value : Module) : String := DottedSExp.print (encodeModule value)
public def decodeModuleText : String → Except DecodeError Module :=
  decodeWire DottedSExp.parse? decodeModule

public def encodeExprText (value : Expr) : String := DottedSExp.print (encodeExpr value)
public def decodeExprText : String → Except DecodeError Expr :=
  decodeWire DottedSExp.parse? decodeExpr

public def encodeModuleBytes (value : Module) : Bytes := DottedSExp.encode (encodeModule value)
public def decodeModuleBytes : Bytes → Except DecodeError Module :=
  decodeWire DottedSExp.decode decodeModule

public def encodeExprBytes (value : Expr) : Bytes := DottedSExp.encode (encodeExpr value)
public def decodeExprBytes : Bytes → Except DecodeError Expr :=
  decodeWire DottedSExp.decode decodeExpr

end Silmaril.ProofFormats.TLA.SurfaceSExp
