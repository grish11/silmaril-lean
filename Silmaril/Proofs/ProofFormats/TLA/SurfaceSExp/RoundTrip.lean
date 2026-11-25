module

public import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
import all Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
import Silmaril.Formats.SExp.Dotted.Thms
import Std.Data.String.ToNat

namespace Silmaril.Proofs.ProofFormats.TLA.SurfaceSExp

open Silmaril.Formats
open Silmaril.ProofFormats.TLA.SurfaceSExp
open Silmaril.Logic.Temporal.TLA.Surface

private theorem check_spine (items : List Tree) :
    (check (SExp2.ofList items)).2 = some (items.map fun item => (check item).1) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [SExp2.ofList, check, ih]

private theorem check_form (tag : String) (fields : List Tree) :
    (check (form tag fields)).1 =
      checkForm (.atom (.symbol tag) :: fields.map fun item => (check item).1) := by
  simp [form, check, symbol, check_spine]

private theorem read_name (value : Ident) :
    readName (check (writeName value)).1 = some value := rfl

private theorem read_text (value : String) :
    readText (check (quoted value)).1 = some value := rfl

private theorem read_nat (value : Nat) :
    readNat (check (writeNat value)).1 = some value := Nat.toNat?_repr value

private theorem read_bool (value : Bool) :
    readBool (check (writeBool value)).1 = some value := by cases value <;> rfl

private theorem check_list {α : Type} (parse : Checked → Option α) (items : List Tree) :
    readList parse (check (form "list" items)).1 =
      items.mapM (fun item => parse (check item).1) := by
  simp [check_form, checkForm, readList, Function.comp_def]

private theorem read_list {α : Type} (write : α → Tree) (parse : Checked → Option α)
    (recover : ∀ value, parse (check (write value)).1 = some value) (items : List α) :
    readList parse (check (writeList write items)).1 = some items := by
  rw [writeList, listForm, check_list]
  induction items with
  | nil => rfl
  | cons item items ih => simp [recover item, ih]

private theorem read_option {α : Type} (write : α → Tree) (parse : Checked → Option α)
    (recover : ∀ value, parse (check (write value)).1 = some value) (value : Option α) :
    readOption parse (check (writeOption write value)).1 = some value := by
  cases value with
  | none => rfl
  | some value =>
    change some <$> parse (check (write value)).1 = some (some value)
    rw [recover value]
    rfl

@[local simp] private theorem read_constructor {α : Type} (kind : Kind α)
    (decode : {β : Type} → Kind β → Option β) :
    readKind kind (.constructor decode) = decode kind := rfl

attribute [local simp] listForm check_form checkForm readFields
attribute [local simp] read_name read_text read_nat read_bool

@[local simp] private theorem recoverNames (items : List Ident) :
    readList readName (check (writeList writeName items)).1 = some items :=
  read_list writeName readName read_name items

@[local simp] private theorem recoverNameOption (value : Option Ident) :
    readOption readName (check (writeOption writeName value)).1 = some value :=
  read_option writeName readName read_name value
attribute [local simp] Function.comp_def

@[local simp] private theorem read_list_node {α : Type} (parse : Checked → Option α)
    (items : List Checked) : readList parse (.list items) = items.mapM parse := rfl

@[local simp] private theorem recoverLiteral (value : Literal) :
    readKind .kLiteral (check (writeLiteral value)).1 = some value := by
  cases value <;> simp [writeLiteral, readLiteralFields]

@[local simp] private theorem recoverPrefixOp (value : PrefixOp) :
    readKind .kPrefixOp (check (writePrefixOp value)).1 = some value := by
  cases value <;> simp [writePrefixOp, readPrefixOpFields]

@[local simp] private theorem recoverInfixOp (value : InfixOp) :
    readKind .kInfixOp (check (writeInfixOp value)).1 = some value := by
  cases value <;> simp [writeInfixOp, readInfixOpFields]

@[local simp] private theorem recoverPostfixOp (value : PostfixOp) :
    readKind .kPostfixOp (check (writePostfixOp value)).1 = some value := by
  cases value <;> simp [writePostfixOp, readPostfixOpFields]

@[local simp] private theorem recoverSymbol (value : Symbol) :
    readKind .kSymbol (check (writeSymbol value)).1 = some value := by
  cases value <;> simp [writeSymbol, readSymbolFields]

@[local simp] private theorem recoverOperatorName (value : OperatorName) :
    readKind .kOperatorName (check (writeOperatorName value)).1 = some value := by
  cases value <;> simp [writeOperatorName, readOperatorNameFields]

@[local simp] private theorem recoverOperatorDecl (value : OperatorDecl) :
    readKind .kOperatorDecl (check (writeOperatorDecl value)).1 = some value := by
  cases value <;> simp [writeOperatorDecl, readOperatorDeclFields]

@[local simp] private theorem recoverOperatorDeclList (items : List OperatorDecl) :
    readList (readKind .kOperatorDecl) (check (writeList writeOperatorDecl items)).1 = some items :=
  read_list writeOperatorDecl (readKind .kOperatorDecl) recoverOperatorDecl items

@[local simp] private theorem recoverOperatorHead (value : OperatorHead) :
    readKind .kOperatorHead (check (writeOperatorHead value)).1 = some value := by
  cases value <;> simp [writeOperatorHead, readOperatorHeadFields]

@[local simp] private theorem recoverBoundPattern (value : BoundPattern) :
    readKind .kBoundPattern (check (writeBoundPattern value)).1 = some value := by
  cases value <;> simp [writeBoundPattern, readBoundPatternFields]

@[local simp] private theorem recoverBoundNames (value : BoundNames) :
    readKind .kBoundNames (check (writeBoundNames value)).1 = some value := by
  cases value <;> simp [writeBoundNames, readBoundNamesFields]

@[local simp] private theorem recoverQuantifier (value : Quantifier) :
    readKind .kQuantifier (check (writeQuantifier value)).1 = some value := by
  cases value <;> simp [writeQuantifier, readQuantifierFields]

@[local simp] private theorem recoverJunction (value : Junction) :
    readKind .kJunction (check (writeJunction value)).1 = some value := by
  cases value <;> simp [writeJunction, readJunctionFields]

@[local simp] private theorem recoverActionBracket (value : ActionBracket) :
    readKind .kActionBracket (check (writeActionBracket value)).1 = some value := by
  cases value <;> simp [writeActionBracket, readActionBracketFields]

@[local simp] private theorem recoverFairness (value : Fairness) :
    readKind .kFairness (check (writeFairness value)).1 = some value := by
  cases value <;> simp [writeFairness, readFairnessFields]

@[local simp] private theorem recoverStructuralSelector (value : StructuralSelector) :
    readKind .kStructuralSelector (check (writeStructuralSelector value)).1 = some value := by
  cases value <;> simp [writeStructuralSelector, readStructuralSelectorFields]

@[local simp] private theorem recoverStepRefLevel (value : StepRefLevel) :
    readKind .kStepRefLevel (check (writeStepRefLevel value)).1 = some value := by
  cases value <;> simp [writeStepRefLevel, readStepRefLevelFields]

@[local simp] private theorem recoverStepRef (value : StepRef) :
    readKind .kStepRef (check (writeStepRef value)).1 = some value := by
  cases value
  simp [writeStepRef, readStepRefFields]

@[local simp] private theorem recoverRefHead (value : RefHead) :
    readKind .kRefHead (check (writeRefHead value)).1 = some value := by
  cases value <;> simp [writeRefHead, readRefHeadFields]

@[local simp] private theorem recoverLabel (value : Label) :
    readKind .kLabel (check (writeLabel value)).1 = some value := by
  cases value
  simp [writeLabel, readLabelFields]

@[local simp] private theorem recoverVisibility (value : Visibility) :
    readKind .kVisibility (check (writeVisibility value)).1 = some value := by
  cases value <;> simp [writeVisibility, readVisibilityFields]

-- This group includes all expression constructors and their nested list spines.
set_option maxHeartbeats 1200000 in
mutual

private theorem recoverExpr : (value : Expr) →
    readKind .kExpr (check (writeExpr value)).1 = some value
  | .ref head args selectors => by
      simp [writeExpr, readExprFields, recoverOpArgItems args, recoverSelectorItems selectors]
  | .literal value => by
      simp [writeExpr, readExprFields]
  | .prefix op arg => by
      simp [writeExpr, readExprFields, recoverExpr arg]
  | .infix op left right => by
      simp [writeExpr, readExprFields, recoverExpr left, recoverExpr right]
  | .postfix op arg => by
      simp [writeExpr, readExprFields, recoverExpr arg]
  | .cartesian factors => by
      simp [writeExpr, readExprFields, recoverExprItems factors]
  | .junction kind items => by
      simp [writeExpr, readExprFields, recoverExprItems items]
  | .ifThenElse condition consequent alternative => by
      simp [writeExpr, readExprFields, recoverExpr condition, recoverExpr consequent,
        recoverExpr alternative]
  | .cases arms other => by
      simp [writeExpr, readExprFields, recoverCaseArmItems arms, recoverExprOption other]
  | .letIn declarations body => by
      simp [writeExpr, readExprFields, recoverLetDeclItems declarations, recoverExpr body]
  | .rigidQuant quantifier binders body => by
      simp [writeExpr, readExprFields, recoverRigidBinders binders, recoverExpr body]
  | .temporalQuant quantifier names body => by
      simp [writeExpr, readExprFields, recoverExpr body]
  | .choose pattern domain predicate => by
      simp [writeExpr, readExprFields, recoverExprOption domain, recoverExpr predicate]
  | .setEnum elements => by
      simp [writeExpr, readExprFields, recoverExprItems elements]
  | .setFilter pattern domain predicate => by
      simp [writeExpr, readExprFields, recoverExpr domain, recoverExpr predicate]
  | .setMap body bounds => by
      simp [writeExpr, readExprFields, recoverExpr body, recoverBoundItems bounds]
  | .function bounds body => by
      simp [writeExpr, readExprFields, recoverBoundItems bounds, recoverExpr body]
  | .functionSet domain range => by
      simp [writeExpr, readExprFields, recoverExpr domain, recoverExpr range]
  | .index fn args => by
      simp [writeExpr, readExprFields, recoverExpr fn, recoverExprItems args]
  | .tuple elements => by
      simp [writeExpr, readExprFields, recoverExprItems elements]
  | .record fields => by
      simp [writeExpr, readExprFields, recoverFieldItems fields]
  | .recordSet fields => by
      simp [writeExpr, readExprFields, recoverFieldItems fields]
  | .field record name => by
      simp [writeExpr, readExprFields, recoverExpr record]
  | .except base updates => by
      simp [writeExpr, readExprFields, recoverExpr base, recoverUpdateItems updates]
  | .oldValue => by
      simp [writeExpr, readExprFields]
  | .action kind body subscript => by
      simp [writeExpr, readExprFields, recoverExpr body, recoverExpr subscript]
  | .fairness kind subscript action => by
      simp [writeExpr, readExprFields, recoverExpr subscript, recoverExpr action]
  | .labeled label body => by
      simp [writeExpr, readExprFields, recoverExpr body]
termination_by structural value => value

private theorem recoverOpArg : (value : OpArg) →
    readKind .kOpArg (check (writeOpArg value)).1 = some value
  | .expr value => by
      simp [writeOpArg, readOpArgFields, recoverExpr value]
  | .symbolic op => by
      simp [writeOpArg, readOpArgFields]
  | .lambda parameters body => by
      simp [writeOpArg, readOpArgFields, recoverExpr body]
termination_by structural value => value

private theorem recoverSelector : (value : Selector) →
    readKind .kSelector (check (writeSelector value)).1 = some value
  | .named name args => by
      simp [writeSelector, readSelectorFields, recoverOpArgItems args]
  | .arguments args => by
      simp [writeSelector, readSelectorFields, recoverOpArgItems args]
  | .structural selector => by
      simp [writeSelector, readSelectorFields]
termination_by structural value => value

private theorem recoverBound : (value : Bound) →
    readKind .kBound (check (writeBound value)).1 = some value
  | .mk names domain => by
      simp [writeBound, readBoundFields, recoverExpr domain]
termination_by structural value => value

private theorem recoverRigidBinders : (value : RigidBinders) →
    readKind .kRigidBinders (check (writeRigidBinders value)).1 = some value
  | .unbounded names => by
      simp [writeRigidBinders, readRigidBindersFields]
  | .bounded groups => by
      simp [writeRigidBinders, readRigidBindersFields, recoverBoundItems groups]
termination_by structural value => value

private theorem recoverCaseArm : (value : CaseArm) →
    readKind .kCaseArm (check (writeCaseArm value)).1 = some value
  | .mk condition result => by
      simp [writeCaseArm, readCaseArmFields, recoverExpr condition, recoverExpr result]
termination_by structural value => value

private theorem recoverField : (value : Field) →
    readKind .kField (check (writeField value)).1 = some value
  | .mk name value => by
      simp [writeField, readFieldFields, recoverExpr value]
termination_by structural value => value

private theorem recoverUpdateComponent : (value : UpdateComponent) →
    readKind .kUpdateComponent (check (writeUpdateComponent value)).1 = some value
  | .field name => by
      simp [writeUpdateComponent, readUpdateComponentFields]
  | .index args => by
      simp [writeUpdateComponent, readUpdateComponentFields, recoverExprItems args]
termination_by structural value => value

private theorem recoverUpdate : (value : Update) →
    readKind .kUpdate (check (writeUpdate value)).1 = some value
  | .mk path value => by
      simp [writeUpdate, readUpdateFields, recoverUpdateComponentItems path, recoverExpr value]
termination_by structural value => value

private theorem recoverSubstitution : (value : Substitution) →
    readKind .kSubstitution (check (writeSubstitution value)).1 = some value
  | .mk target replacement => by
      simp [writeSubstitution, readSubstitutionFields, recoverOpArg replacement]
termination_by structural value => value

private theorem recoverInstantiation : (value : Instantiation) →
    readKind .kInstantiation (check (writeInstantiation value)).1 = some value
  | .mk moduleName substitutions => by
      simp [writeInstantiation, readInstantiationFields, recoverSubstitutionItems substitutions]
termination_by structural value => value

private theorem recoverDefinition : (value : Definition) →
    readKind .kDefinition (check (writeDefinition value)).1 = some value
  | .operator visibility head body => by
      simp [writeDefinition, readDefinitionFields, recoverExpr body]
  | .function visibility name bounds body => by
      simp [writeDefinition, readDefinitionFields, recoverBoundItems bounds, recoverExpr body]
  | .namedInstance visibility name parameters instanceBody => by
      simp [writeDefinition, readDefinitionFields, recoverInstantiation instanceBody]
termination_by structural value => value

private theorem recoverLetDecl : (value : LetDecl) →
    readKind .kLetDecl (check (writeLetDecl value)).1 = some value
  | .definition value => by
      simp [writeLetDecl, readLetDeclFields, recoverDefinition value]
  | .recursive operators => by
      simp [writeLetDecl, readLetDeclFields]
termination_by structural value => value

private theorem recoverOpArgItems : (items : List OpArg) →
    (writeOpArgItems items).mapM (fun item => readKind .kOpArg (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeOpArgItems, recoverOpArg item, recoverOpArgItems items]
termination_by structural items => items

private theorem recoverSelectorItems : (items : List Selector) →
    (writeSelectorItems items).mapM (fun item => readKind .kSelector (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeSelectorItems, recoverSelector item, recoverSelectorItems items]
termination_by structural items => items

private theorem recoverExprItems : (items : List Expr) →
    (writeExprItems items).mapM (fun item => readKind .kExpr (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeExprItems, recoverExpr item, recoverExprItems items]
termination_by structural items => items

private theorem recoverCaseArmItems : (items : List CaseArm) →
    (writeCaseArmItems items).mapM (fun item => readKind .kCaseArm (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeCaseArmItems, recoverCaseArm item, recoverCaseArmItems items]
termination_by structural items => items

private theorem recoverExprOption : (value : Option Expr) →
    readOption (readKind .kExpr) (check (writeExprOption value)).1 = some value
  | none => by simp [writeExprOption, checkForm, readOption]
  | some value => by
      simp [writeExprOption, checkForm, readOption, recoverExpr value]
termination_by structural value => value

private theorem recoverLetDeclItems : (items : List LetDecl) →
    (writeLetDeclItems items).mapM (fun item => readKind .kLetDecl (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeLetDeclItems, recoverLetDecl item, recoverLetDeclItems items]
termination_by structural items => items

private theorem recoverBoundItems : (items : List Bound) →
    (writeBoundItems items).mapM (fun item => readKind .kBound (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeBoundItems, recoverBound item, recoverBoundItems items]
termination_by structural items => items

private theorem recoverFieldItems : (items : List Field) →
    (writeFieldItems items).mapM (fun item => readKind .kField (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeFieldItems, recoverField item, recoverFieldItems items]
termination_by structural items => items

private theorem recoverUpdateItems : (items : List Update) →
    (writeUpdateItems items).mapM (fun item => readKind .kUpdate (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeUpdateItems, recoverUpdate item, recoverUpdateItems items]
termination_by structural items => items

private theorem recoverUpdateComponentItems : (items : List UpdateComponent) →
    (writeUpdateComponentItems items).mapM (fun item => readKind .kUpdateComponent (check item).1) =
      some items
  | [] => rfl
  | item :: items => by
    simp [writeUpdateComponentItems, recoverUpdateComponent item, recoverUpdateComponentItems items]
termination_by structural items => items

private theorem recoverSubstitutionItems : (items : List Substitution) →
    (writeSubstitutionItems items).mapM (fun item => readKind .kSubstitution (check item).1) = some items
  | [] => rfl
  | item :: items => by
    simp [writeSubstitutionItems, recoverSubstitution item, recoverSubstitutionItems items]
termination_by structural items => items

end

attribute [local simp] recoverExpr recoverRigidBinders recoverInstantiation recoverDefinition

@[local simp] private theorem recoverExprList (items : List Expr) :
    readList (readKind .kExpr) (check (writeList writeExpr items)).1 = some items :=
  read_list writeExpr (readKind .kExpr) recoverExpr items

@[local simp] private theorem recoverDefinitionList (items : List Definition) :
    readList (readKind .kDefinition) (check (writeList writeDefinition items)).1 = some items :=
  read_list writeDefinition (readKind .kDefinition) recoverDefinition items

@[local simp] private theorem recoverSymbolLevel (value : SymbolLevel) :
    readKind .kSymbolLevel (check (writeSymbolLevel value)).1 = some value := by
  cases value <;> simp [writeSymbolLevel, readSymbolLevelFields]

@[local simp] private theorem recoverAssumeProveMode (value : AssumeProveMode) :
    readKind .kAssumeProveMode (check (writeAssumeProveMode value)).1 = some value := by
  cases value <;> simp [writeAssumeProveMode, readAssumeProveModeFields]

mutual

private theorem recoverStatement : (value : Statement) →
    readKind .kStatement (check (writeStatement value)).1 = some value
  | .expr value => by
      simp [writeStatement, readStatementFields]
  | .assumeProve assumeMode hypotheses proveMode goal => by
      simp [writeStatement, readStatementFields, recoverHypothesisItems hypotheses]
  | .labeled name statement => by
      simp [writeStatement, readStatementFields, recoverStatement statement]
termination_by structural value => value

private theorem recoverHypothesis : (value : Hypothesis) →
    readKind .kHypothesis (check (writeHypothesis value)).1 = some value
  | .statement value => by
      simp [writeHypothesis, readHypothesisFields, recoverStatement value]
  | .newSymbol level declaration => by
      simp [writeHypothesis, readHypothesisFields]
  | .newVariable name => by
      simp [writeHypothesis, readHypothesisFields]
  | .newBoundConstant name domain => by
      simp [writeHypothesis, readHypothesisFields]
termination_by structural value => value

private theorem recoverHypothesisItems : (items : List Hypothesis) →
    (writeHypothesisItems items).mapM (fun item => readKind .kHypothesis (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeHypothesisItems, recoverHypothesis item, recoverHypothesisItems items]
termination_by structural items => items

end

attribute [local simp] recoverStatement

@[local simp] private theorem recoverCitation (value : Citation) :
    readKind .kCitation (check (writeCitation value)).1 = some value := by
  cases value <;> simp [writeCitation, readCitationFields]

@[local simp] private theorem recoverCitationList (items : List Citation) :
    readList (readKind .kCitation) (check (writeList writeCitation items)).1 = some items :=
  read_list writeCitation (readKind .kCitation) recoverCitation items

@[local simp] private theorem recoverCitations (value : Citations) :
    readKind .kCitations (check (writeCitations value)).1 = some value := by
  cases value
  simp [writeCitations, readCitationsFields]

@[local simp] private theorem recoverDirective (value : Directive) :
    readKind .kDirective (check (writeDirective value)).1 = some value := by
  cases value <;> simp [writeDirective, readDirectiveFields]

@[local simp] private theorem recoverStepLevel (value : StepLevel) :
    readKind .kStepLevel (check (writeStepLevel value)).1 = some value := by
  cases value <;> simp [writeStepLevel, readStepLevelFields]

@[local simp] private theorem recoverStepLabel (value : StepLabel) :
    readKind .kStepLabel (check (writeStepLabel value)).1 = some value := by
  cases value
  simp [writeStepLabel, readStepLabelFields]

mutual

private theorem recoverProof : (value : Proof) →
    readKind .kProof (check (writeProof value)).1 = some value
  | .obvious => by
      simp [writeProof, readProofFields]
  | .omitted => by
      simp [writeProof, readProofFields]
  | .byFacts only citations => by
      simp [writeProof, readProofFields]
  | .steps steps qedLabel qedProof => by
      simp [writeProof, readProofFields, recoverProofStepItems steps, recoverProofOption qedProof]
termination_by structural value => value

private theorem recoverProofStep : (value : ProofStep) →
    readKind .kProofStep (check (writeProofStep value)).1 = some value
  | .mk label body => by
      simp [writeProofStep, readProofStepFields, recoverStepBody body]
termination_by structural value => value

private theorem recoverStepBody : (value : StepBody) →
    readKind .kStepBody (check (writeStepBody value)).1 = some value
  | .directive value => by
      simp [writeStepBody, readStepBodyFields]
  | .instantiation value => by
      simp [writeStepBody, readStepBodyFields]
  | .define definitions => by
      simp [writeStepBody, readStepBodyFields]
  | .have value => by
      simp [writeStepBody, readStepBodyFields]
  | .take binders => by
      simp [writeStepBody, readStepBodyFields]
  | .witness values => by
      simp [writeStepBody, readStepBodyFields]
  | .pick binders predicate proof => by
      simp [writeStepBody, readStepBodyFields, recoverProofOption proof]
  | .caseOf condition proof => by
      simp [writeStepBody, readStepBodyFields, recoverProofOption proof]
  | .assert statement proof => by
      simp [writeStepBody, readStepBodyFields, recoverProofOption proof]
  | .suffices statement proof => by
      simp [writeStepBody, readStepBodyFields, recoverProofOption proof]
termination_by structural value => value

private theorem recoverProofStepItems : (items : List ProofStep) →
    (writeProofStepItems items).mapM (fun item => readKind .kProofStep (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeProofStepItems, recoverProofStep item, recoverProofStepItems items]
termination_by structural items => items

private theorem recoverProofOption : (value : Option Proof) →
    readOption (readKind .kProof) (check (writeProofOption value)).1 = some value
  | none => by simp [writeProofOption, checkForm, readOption]
  | some value => by
      simp [writeProofOption, checkForm, readOption, recoverProof value]
termination_by structural value => value

end

attribute [local simp] recoverProof

@[local simp] private theorem recoverOptionalProof (value : Option Proof) :
    readOption (readKind .kProof) (check (writeOption writeProof value)).1 = some value :=
  read_option writeProof (readKind .kProof) recoverProof value

@[local simp] private theorem recoverTheorem (value : Theorem) :
    readKind .kTheorem (check (writeTheorem value)).1 = some value := by
  cases value
  simp [writeTheorem, readTheoremFields]

mutual

private theorem recoverModule : (value : Module) →
    readKind .kModule (check (writeModule value)).1 = some value
  | .mk name extendsModules units => by
      simp [writeModule, readModuleFields, recoverModuleUnitItems units]
termination_by structural value => value

private theorem recoverModuleUnit : (value : ModuleUnit) →
    readKind .kModuleUnit (check (writeModuleUnit value)).1 = some value
  | .variables names => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .constants operators => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .recursive operators => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .definition value => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .instantiation visibility value => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .assumption name body => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .theoremDecl value => by
      simp [writeModuleUnit, readModuleUnitFields]
  | .submodule value => by
      simp [writeModuleUnit, readModuleUnitFields, recoverModule value]
  | .directive value => by
      simp [writeModuleUnit, readModuleUnitFields]
termination_by structural value => value

private theorem recoverModuleUnitItems : (items : List ModuleUnit) →
    (writeModuleUnitItems items).mapM (fun item => readKind .kModuleUnit (check item).1) = some items
  | [] => rfl
  | item :: items => by simp [writeModuleUnitItems, recoverModuleUnit item, recoverModuleUnitItems items]
termination_by structural items => items

end

private theorem decodeRoot_envelope {α : Type} (kind : Kind α) (write : α → Tree) (value : α)
    (recover : readKind kind (check (write value)).1 = some value) :
    decodeRoot kind (fun x => envelope (write x)) (envelope (write value)) = .ok value := by
  have payload_eq : payload? (envelope (write value)) = some (write value) := rfl
  simp [decodeRoot, payload_eq, recover]

private theorem encode_of_decodeRoot {α : Type} (kind : Kind α) (encode : α → Tree)
    {tree : Tree} {value : α} (accepted : decodeRoot kind encode tree = .ok value) :
    encode value = tree := by
  unfold decodeRoot at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted
        assumption
      · contradiction
    · contradiction
  · contradiction

public theorem decodeModule_encodeModule (value : Module) :
    decodeModule (encodeModule value) = .ok value :=
  decodeRoot_envelope .kModule writeModule value (recoverModule value)

public theorem encodeModule_of_decodeModule {tree : Tree} {value : Module}
    (accepted : decodeModule tree = .ok value) : encodeModule value = tree :=
  encode_of_decodeRoot .kModule encodeModule accepted

public theorem decodeModuleText_encodeModuleText (value : Module) :
    decodeModuleText (encodeModuleText value) = .ok value := by
  simp [decodeModuleText, encodeModuleText, decodeWire, DottedSExp.parse?_print,
    decodeModule_encodeModule]

public theorem decodeModuleBytes_encodeModuleBytes (value : Module) :
    decodeModuleBytes (encodeModuleBytes value) = .ok value := by
  simp [decodeModuleBytes, encodeModuleBytes, decodeWire, DottedSExp.decode_encode,
    decodeModule_encodeModule]

public theorem decodeExpr_encodeExpr (value : Expr) :
    decodeExpr (encodeExpr value) = .ok value :=
  decodeRoot_envelope .kExpr writeExpr value (recoverExpr value)

public theorem encodeExpr_of_decodeExpr {tree : Tree} {value : Expr}
    (accepted : decodeExpr tree = .ok value) : encodeExpr value = tree :=
  encode_of_decodeRoot .kExpr encodeExpr accepted

public theorem decodeExprText_encodeExprText (value : Expr) :
    decodeExprText (encodeExprText value) = .ok value := by
  simp [decodeExprText, encodeExprText, decodeWire, DottedSExp.parse?_print, decodeExpr_encodeExpr]

public theorem decodeExprBytes_encodeExprBytes (value : Expr) :
    decodeExprBytes (encodeExprBytes value) = .ok value := by
  simp [decodeExprBytes, encodeExprBytes, decodeWire, DottedSExp.decode_encode,
    decodeExpr_encodeExpr]

end Silmaril.Proofs.ProofFormats.TLA.SurfaceSExp
