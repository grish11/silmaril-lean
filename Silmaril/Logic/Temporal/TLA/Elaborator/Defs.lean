module

public import Silmaril.Logic.Temporal.TLA.Kernel.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Defs

/-! # Scalar TLA+ surface elaboration

Check ordered declarations and elaborate scalar expressions to kernel denotations.
See `docs/projects/tla-elaborator.md` for the fragment and import contract.
-/

public section

namespace Silmaril.Logic.Temporal.TLA.Elaborator

open Surface (Expr Ident)
open Kernel (Scalar Value Scope State StatePredicate StepPredicate Term)

/-- Caller-supplied sorts for exactly the module's flexible variables. -/
abbrev Signature := List (Ident × Scalar)

/-- A state is indexed by declared variable name and sort. Module checking rejects
repeated names before using this scope. -/
@[expose] def Signature.scope (signature : Signature) : Scope where
  rigid _ := Empty
  flex sort := { name : Ident // signature.lookup name = some sort }

@[expose] def Signature.noRigid (signature : Signature) : Kernel.RigidEnv signature.scope :=
  fun _ name => nomatch name

/-- Identities of the supported libraries in the pinned Apalache distribution.
Passing an identity attests that imports of that name resolve to that library. -/
inductive StandardModule where
  | integers | sequences | finiteSets | tlc | apalache | variants
  deriving DecidableEq, Repr

def StandardModule.moduleName : StandardModule → Ident
  | .integers => "Integers"
  | .sequences => "Sequences"
  | .finiteSets => "FiniteSets"
  | .tlc => "TLC"
  | .apalache => "Apalache"
  | .variants => "Variants"

inductive Diagnostic where
  | unresolvedImport (name : Ident)
  | duplicateImport (name : Ident)
  | selfImport (name : Ident)
  | duplicateSort (name : Ident)
  | missingSort (name : Ident)
  | unexpectedSort (name : Ident)
  | conflictingName (name : Ident)
  | unknownName (name : Ident)
  | nameOutsideFragment (name : Ident)
  | expectedOperator (name : Ident)
  | arityMismatch (name : Ident) (expected actual : Nat)
  | typeMismatch (expected actual : Scalar)
  | actionInState (name : Ident)
  | primeOfAction
  | requiresImport (operator : String) (library : StandardModule)
  | unsupportedOperator (spelling : String)
  | unsupportedExpression (form : String)
  | unsupportedDeclaration (form : String)
  | inDefinition (name : Ident) (cause : Diagnostic)
  deriving DecidableEq

/-- A checked Boolean operator keeps its expression level. The `state` case
includes constant expressions. -/
inductive CheckedPredicate (Γ : Scope) where
  | state (predicate : StatePredicate Γ)
  | action (predicate : StepPredicate Γ)

structure CheckedModule (signature : Signature) where
  private mk ::
  predicate : Ident → Except Diagnostic (CheckedPredicate signature.scope)

@[expose] def CheckedModule.statePredicate {signature : Signature} (checked : CheckedModule signature)
    (name : Ident) : Except Diagnostic (StatePredicate signature.scope) :=
  match checked.predicate name with
  | .ok (.state p) => .ok p
  | .ok (.action _) => .error (.actionInState name)
  | .error e => .error e

/-- State-level predicates in a step read its source. -/
@[expose] def CheckedModule.stepPredicate {signature : Signature} (checked : CheckedModule signature)
    (name : Ident) : Except Diagnostic (StepPredicate signature.scope) :=
  match checked.predicate name with
  | .ok (.state p) => .ok p.current
  | .ok (.action p) => .ok p
  | .error e => .error e

@[expose] def CheckedModule.stateDenotation {signature : Signature} (checked : CheckedModule signature)
    (name : Ident) : Except Diagnostic (General.StatePred Value signature.scope) :=
  (checked.statePredicate name).map Kernel.Predicate.toStatePred

@[expose] def CheckedModule.actionDenotation {signature : Signature} (checked : CheckedModule signature)
    (name : Ident) : Except Diagnostic (General.Action Value signature.scope) :=
  (checked.stepPredicate name).map Kernel.Predicate.toAction

private def StandardModule.exportedNames : StandardModule → List Ident
  | .integers => ["Nat", "Int"]
  | .sequences => ["Seq", "Len", "Append", "Head", "Tail", "SubSeq", "SelectSeq"]
  | .finiteSets => ["IsFiniteSet", "Cardinality"]
  | .tlc => ["Print", "PrintT", "Assert", "JavaTime", "TLCGet", "TLCSet", "Permutations",
      "SortSeq", "RandomElement", "Any", "ToString", "TLCEval"]
  | .apalache => ["Gen", "Guess", "SetAsFun", "MkSeq", "FunAsSeq", "Skolem", "Expand",
      "ConstCardinality", "ApaFoldSet", "ApaFoldSeqLeft", "Repeat"]
  | .variants => ["UNIT", "Variant", "VariantFilter", "VariantTag", "VariantGetOrElse",
      "VariantGetUnsafe"]

private abbrev Imports := List StandardModule

private def resolveImports (available : Imports) (source : Surface.Module) :
    Except Diagnostic Imports := do
  let mut resolved : Imports := []
  for name in source.extendsModules do
    if name == source.name then throw (.selfImport name)
    let some library := available.find? (fun library => library.moduleName == name)
      | throw (.unresolvedImport name)
    if library ∈ resolved then throw (.duplicateImport name)
    resolved := library :: resolved
  return resolved

private def requireImport (imports : Imports) (op : String) (library : StandardModule) :
    Except Diagnostic Unit :=
  unless library ∈ imports do throw (.requiresImport op library)

private def knownUnsupportedName (imports : Imports) (name : Ident) : Bool :=
  name == "BOOLEAN" || name == "STRING" || imports.any (·.exportedNames.contains name)

private def Meaning (Γ : Scope) (Input : Type) : Scalar → Type
  | .int => Term Γ Input Int
  | .bool => Kernel.Predicate Γ Input

private inductive Checked (Γ : Scope) (sort : Scalar) where
  | state (meaning : Meaning Γ (State Γ) sort)
  | action (meaning : Meaning Γ (State Γ × State Γ) sort)

private abbrev ScalarExpr (Γ : Scope) := (sort : Scalar) × Checked Γ sort

private variable {Γ : Scope} {a b c : Scalar}

private def Meaning.ofTerm {Input : Type} (sort : Scalar) (term : Term Γ Input (Value sort)) :
    Meaning Γ Input sort :=
  match sort with
  | .int => term
  | .bool => Kernel.Predicate.ofBool term

private def Meaning.asTerm {Input : Type} (sort : Scalar) (meaning : Meaning Γ Input sort) :
    Term Γ Input (Value sort) :=
  match sort with
  | .int => meaning
  | .bool => Kernel.Predicate.check meaning

private def Checked.literal (sort : Scalar) (value : Value sort) : Checked Γ sort :=
  .state (Meaning.ofTerm sort (Term.literal value))

private def Checked.toStep : Checked Γ a → Meaning Γ (State Γ × State Γ) a
  | .action e => e
  | .state e => match a with
    | .int => Term.current e
    | .bool => Kernel.Predicate.current e

private def Checked.prime : Checked Γ a → Except Diagnostic (Checked Γ a)
  | .action _ => throw .primeOfAction
  | .state e => pure (.action (match a with
    | .int => Term.next e
    | .bool => Kernel.Predicate.next e))

private def Checked.map (f : ∀ {Input}, Meaning Γ Input a → Meaning Γ Input b) :
    Checked Γ a → Checked Γ b
  | .state e => .state (f e)
  | .action e => .action (f e)

private def Checked.combine
    (f : ∀ {Input}, Meaning Γ Input a → Meaning Γ Input b → Meaning Γ Input c)
    (left : Checked Γ a) (right : Checked Γ b) : Checked Γ c :=
  match left, right with
  | .state l, .state r => .state (f l r)
  | l, r => .action (f l.toStep r.toStep)

private def Meaning.ite {Input : Type} (sort : Scalar) (test : Kernel.Predicate Γ Input)
    (yes no : Meaning Γ Input sort) : Meaning Γ Input sort :=
  match sort with
  | .int => Term.ite test yes no
  | .bool => (test.and yes).or (test.not.and no)

private def Checked.ite (test : Checked Γ .bool) (yes no : Checked Γ a) : Checked Γ a :=
  match test, yes, no with
  | .state t, .state y, .state n => .state (Meaning.ite a t y n)
  | t, y, n => .action (Meaning.ite a t.toStep y.toStep n.toStep)

private def Checked.weaken (sort : Scalar) : Checked Γ a → Checked (Γ.bindRigid sort) a
  | .state e => .state (match a with
    | .int => Term.weakenRigid e sort
    | .bool => Kernel.Predicate.weakenRigid e sort)
  | .action e => .action (match a with
    | .int => Term.weakenRigid e sort
    | .bool => Kernel.Predicate.weakenRigid e sort)

private def Checked.expect (e : ScalarExpr Γ) (expected : Scalar) :
    Except Diagnostic (Checked Γ expected) :=
  if h : e.1 = expected then pure (h ▸ e.2) else throw (.typeMismatch expected e.1)

private def Checked.existsIn (values : List (Value a)) :
    Checked (Γ.bindRigid a) .bool → Checked Γ .bool
  | .state p => .state (Kernel.Predicate.existsIn (Term.literal values) p)
  | .action p => .action (Kernel.Predicate.existsIn (Term.literal values) p)

private def compareScalars (negated : Bool) (left right : ScalarExpr Γ) :
    Except Diagnostic (ScalarExpr Γ) := do
  let r ← Checked.expect right left.1
  return ⟨.bool, left.2.combine (fun l r =>
    let equal := Kernel.Predicate.eq (Meaning.asTerm left.1 l) (Meaning.asTerm left.1 r)
    if negated then equal.not else equal) r⟩

private def elabInfix (imports : Imports) (op : String) (left right : ScalarExpr Γ) :
    Except Diagnostic (ScalarExpr Γ) := do
  match op with
  | "=" => compareScalars false left right
  | "#" | "/=" | "≠" => compareScalars true left right
  | ":=" | "≔" =>
    requireImport imports op .apalache
    compareScalars false left right
  | "/\\" | "\\land" | "∧" => boolean Kernel.Predicate.and
  | "\\/" | "\\lor" | "∨" => boolean Kernel.Predicate.or
  | "=>" | "⇒" => boolean Kernel.Predicate.implies
  | "<=>" | "\\equiv" | "≡" | "⇔" => boolean Kernel.Predicate.iff
  | "+" => integer .int Term.add
  | "-" => integer .int Term.sub
  | "*" => integer .int Term.mul
  | "<" => integer .bool Kernel.Predicate.lt
  | ">" => integer .bool (fun l r => Kernel.Predicate.lt r l)
  | "<=" | "=<" | "\\leq" | "≤" => integer .bool Kernel.Predicate.le
  | ">=" | "\\geq" | "≥" => integer .bool (fun l r => Kernel.Predicate.le r l)
  | _ => throw (.unsupportedOperator op)
where
  boolean (f : ∀ {Input}, Meaning Γ Input .bool → Meaning Γ Input .bool → Meaning Γ Input .bool) :
      Except Diagnostic (ScalarExpr Γ) := do
    return ⟨.bool, (← Checked.expect left .bool).combine f (← Checked.expect right .bool)⟩
  integer (sort : Scalar)
      (f : ∀ {Input}, Meaning Γ Input .int → Meaning Γ Input .int → Meaning Γ Input sort) :
      Except Diagnostic (ScalarExpr Γ) := do
    requireImport imports op .integers
    return ⟨sort, (← Checked.expect left .int).combine f (← Checked.expect right .int)⟩

private structure Binding (Γ : Scope) where
  isOperator : Bool
  value : ScalarExpr Γ

private abbrev Locals (Γ : Scope) := List (Ident × Binding Γ)

private def ensureFresh (imports : Imports) (locals : Locals Γ) (name : Ident) :
    Except Diagnostic Unit := do
  if name == "TRUE" || name == "FALSE" || knownUnsupportedName imports name ||
      (locals.lookup name).isSome then
    throw (.conflictingName name)

private def resolveName (imports : Imports) (locals : Locals Γ) (name : Ident) (argc : Nat) :
    Except Diagnostic (ScalarExpr Γ) := do
  let value ← match locals.lookup name with
    | some binding => pure binding.value
    | none => match name with
      | "TRUE" => pure ⟨.bool, Checked.literal .bool true⟩
      | "FALSE" => pure ⟨.bool, Checked.literal .bool false⟩
      | _ => if knownUnsupportedName imports name then throw (.nameOutsideFragment name)
             else throw (.unknownName name)
  if argc != 0 then throw (.arityMismatch name 0 argc)
  return value

private def setElement (imports : Imports) : Expr → Except Diagnostic ((sort : Scalar) × Value sort)
  | .literal (.natural n) => pure ⟨.int, Int.ofNat n⟩
  | .prefix .minus (.literal (.natural n)) => do
    requireImport imports "unary -" .integers
    return ⟨.int, -Int.ofNat n⟩
  | .ref (.operator (.ident "FALSE")) [] [] => pure ⟨.bool, false⟩
  | .ref (.operator (.ident "TRUE")) [] [] => pure ⟨.bool, true⟩
  | _ => throw (.unsupportedExpression "nonliteral finite-set element")

private def bindRigid (locals : Locals Γ) (name : Ident) (sort : Scalar) : Locals (Γ.bindRigid sort) :=
  let value := Kernel.Term.rigid (a := sort) (Γ.rigid.fresh sort)
  (name, ⟨false, ⟨sort, .state (Meaning.ofTerm sort value)⟩⟩) ::
    locals.map fun (key, binding) =>
      (key, ⟨binding.isOperator, ⟨binding.value.1, binding.value.2.weaken sort⟩⟩)

mutual

private def elabExpr {Γ : Scope} (imports : Imports) (expr : Expr) (locals : Locals Γ) :
    Except Diagnostic (ScalarExpr Γ) := do
  match expr with
  | .ref (.operator (.ident name)) args [] => resolveName imports locals name args.length
  | .ref .. => throw (.unsupportedExpression "qualified, symbolic or proof reference")
  | .literal (.natural n) => pure ⟨.int, Checked.literal .int (Int.ofNat n)⟩
  | .prefix .minus arg =>
    requireImport imports "unary -" .integers
    return ⟨.int, (← Checked.expect (← elabExpr imports arg locals) .int).map (a := .int) Term.neg⟩
  | .prefix .negation arg =>
    let p ← Checked.expect (← elabExpr imports arg locals) .bool
    return ⟨.bool, p.map (a := .bool) Kernel.Predicate.not⟩
  | .infix (.symbol op) left right =>
    elabInfix imports op (← elabExpr imports left locals) (← elabExpr imports right locals)
  | .postfix .prime arg =>
    let ⟨sort, meaning⟩ ← elabExpr imports arg locals
    return ⟨sort, ← meaning.prime⟩
  | .ifThenElse test yes no =>
    let condition ← Checked.expect (← elabExpr imports test locals) .bool
    let ⟨sort, yes⟩ ← elabExpr imports yes locals
    let no ← Checked.expect (← elabExpr imports no locals) sort
    return ⟨sort, condition.ite yes no⟩
  | .junction kind items => return ⟨.bool, ← elabJunction imports kind items locals⟩
  | .rigidQuant .exists (.bounded [⟨.names [name], .setEnum (first :: rest)⟩]) body =>
    ensureFresh imports locals name
    let ⟨sort, value⟩ ← setElement imports first
    let values ← rest.mapM fun expr => do
      let ⟨actual, value⟩ ← setElement imports expr
      if h : actual = sort then pure (h ▸ value) else throw (.typeMismatch sort actual)
    let p ← Checked.expect (← elabExpr (Γ := Γ.bindRigid sort) imports body (bindRigid locals name sort)) .bool
    return ⟨.bool, Checked.existsIn (value :: values) p⟩
  | .rigidQuant .. => throw (.unsupportedExpression "rigid quantifier outside the literal-set fragment")
  | .action .. => throw (.unsupportedExpression "action bracket")
  | .fairness .. => throw (.unsupportedExpression "fairness")
  | .except .. | .oldValue => throw (.unsupportedExpression "EXCEPT or @")
  | _ => throw (.unsupportedExpression "scalar state/action fragment")
termination_by structural expr

private def elabJunction {Γ : Scope} (imports : Imports) (kind : Surface.Junction) (items : List Expr)
    (locals : Locals Γ) : Except Diagnostic (Checked Γ .bool) := do
  match items with
  | [] => throw (.unsupportedExpression "empty junction")
  | [item] => Checked.expect (← elabExpr imports item locals) .bool
  | item :: rest =>
    let p ← Checked.expect (← elabExpr imports item locals) .bool
    let q ← elabJunction imports kind rest locals
    return match kind with
    | .conjunction => p.combine (a := .bool) (b := .bool) Kernel.Predicate.and q
    | .disjunction => p.combine (a := .bool) (b := .bool) Kernel.Predicate.or q
termination_by structural items

end

private def addVariable (signature : Signature) (imports : Imports) (name : Ident)
    (locals : Locals signature.scope) : Except Diagnostic (Locals signature.scope) := do
  ensureFresh imports locals name
  match h : signature.lookup name with
  | none => throw (.missingSort name)
  | some sort =>
    let term := Term.flex (Γ := signature.scope) (a := sort) ⟨name, h⟩
    return (name, ⟨false, ⟨sort, .state (Meaning.ofTerm sort term)⟩⟩) :: locals

private def checkUnit (signature : Signature) (imports : Imports) (unit : Surface.ModuleUnit)
    (locals : Locals signature.scope) : Except Diagnostic (Locals signature.scope) := do
  match unit with
  | .variables names =>
    if names.isEmpty then throw (.unsupportedDeclaration "empty VARIABLE declaration")
    names.foldlM (fun ctx name => addVariable signature imports name ctx) locals
  | .definition (.operator _ (.ident name []) body) =>
    ensureFresh imports locals name
    let value ← (elabExpr imports body locals).mapError (.inDefinition name)
    return (name, ⟨true, value⟩) :: locals
  | .definition _ =>
    throw (.unsupportedDeclaration "definition other than a nullary identifier operator")
  | .assumption .. => throw (.unsupportedDeclaration "ASSUME")
  | .constants _ => throw (.unsupportedDeclaration "CONSTANT")
  | .recursive _ => throw (.unsupportedDeclaration "RECURSIVE")
  | .instantiation .. => throw (.unsupportedDeclaration "INSTANCE")
  | .submodule _ => throw (.unsupportedDeclaration "submodule")
  | .theoremDecl _ => throw (.unsupportedDeclaration "theorem")
  | .directive _ => throw (.unsupportedDeclaration "proof directive")

/-- Check every unit in declaration order. Only libraries both attested by the
caller and named in `EXTENDS` enter resolution. -/
def elaborate (available : List StandardModule) (signature : Signature) (source : Surface.Module) :
    Except Diagnostic (CheckedModule signature) := do
  let imports ← resolveImports available source
  let mut seen : List Ident := []
  for (name, _) in signature do
    if name ∈ seen then throw (.duplicateSort name)
    seen := name :: seen
  let locals ← source.units.foldlM (fun locals unit => checkUnit signature imports unit locals) []
  for (name, _) in signature do
    unless ((locals.lookup name).any (fun binding => !binding.isOperator)) do
      throw (.unexpectedSort name)
  return ⟨fun name => do
    let some binding := locals.lookup name | throw (.unknownName name)
    unless binding.isOperator do throw (.expectedOperator name)
    match ← Checked.expect binding.value .bool with
    | .state p => pure (.state p)
    | .action p => pure (.action p)⟩

end Silmaril.Logic.Temporal.TLA.Elaborator
