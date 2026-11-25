module

public import Silmaril.Languages.Starlark.Lists.Iteration.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions

open Lists

structure Parameter where
  slot : Binding
  defaultExpr : Option Lists.Expr := none

/-- Parameters before the star can be filled positionally or by name. -/
structure Signature where
  positional : List Parameter := []
  keywordOnly : List Parameter := []
  varargs : Option Binding := none
  kwargs : Option Binding := none

def Signature.named (signature : Signature) : List Parameter :=
  signature.positional ++ signature.keywordOnly

def Signature.defaulted (signature : Signature) : List (Binding × Lists.Expr) :=
  signature.named.filterMap fun p => p.defaultExpr.map fun expr => (p.slot, expr)

def Signature.slots (signature : Signature) : List Binding :=
  signature.named.map Parameter.slot ++ signature.varargs.toList ++ signature.kwargs.toList

structure Arguments where
  positional : List Lists.Expr := []
  keywords : List (String × Lists.Expr) := []
  star : Option Lists.Expr := none
  starStar : Option Lists.Expr := none

def operandList (expressions : List Lists.Expr) : Code (List Lists.Value) :=
  expressions.foldr Code.cons .empty

def Arguments.operands (callee : Lists.Expr) (args : Arguments) : Code (List Lists.Value) :=
  operandList (callee :: (args.positional ++ args.keywords.map Prod.snd ++
    args.star.toList ++ args.starStar.toList))

inductive CallStaticError where
  | duplicateParameter (name : String)
  | requiredAfterDefault (name : String)
  | bareStarWithoutOptional
  | duplicateExplicitKeyword (name : String)
  deriving DecidableEq, Repr

def firstDuplicate : List String → Option String
  | [] => none
  | name :: rest => if rest.contains name then some name else firstDuplicate rest

def Signature.validate (signature : Signature) : Except CallStaticError Unit := do
  if let some duplicate := firstDuplicate (signature.slots.map Binding.name) then
    throw (.duplicateParameter duplicate)
  let optionalSuffix := signature.positional.dropWhile fun p => p.defaultExpr.isNone
  if let some required := optionalSuffix.find? (fun p => p.defaultExpr.isNone) then
    throw (.requiredAfterDefault required.slot.name)
  if signature.varargs.isNone && !signature.keywordOnly.isEmpty &&
      signature.keywordOnly.all (fun p => p.defaultExpr.isNone) then
    throw .bareStarWithoutOptional

def Arguments.validate (args : Arguments) : Except CallStaticError Unit := do
  if let some duplicate := firstDuplicate (args.keywords.map Prod.fst) then
    throw (.duplicateExplicitKeyword duplicate)

/-- Positional and string-named values after operand evaluation and expansion. -/
structure Actual where
  positional : List Lists.Value
  keywords : List (String × Lists.Value)

def expandStar : Option Lists.Value → Meaning (List Lists.Value)
  | none => pure []
  | some (.list address) => listElements address
  | some (.tuple address) => tupleElements address
  | some (.dict address) => (List.map Entry.key) <$> dictEntries address
  | some _ => throw .invalidStar

def expandStarStar : Option Lists.Value → Meaning (List (String × Lists.Value))
  | none => pure []
  | some (.dict address) => do
    let entries ← dictEntries address
    fromExcept (entries.mapM fun entry =>
      match entry.key with
      | .string name => .ok (name, entry.value)
      | key => .error (.keywordMustBeString key))
  | some _ => throw .invalidStarStar

/-- All operands have already run. Validate the mapping expansion before the
iterable expansion, following the pinned Go call instruction. -/
def Arguments.expand (args : Arguments) (values : List Lists.Value) : Meaning Actual := do
  let positional := values.take args.positional.length
  let afterPositional := values.drop args.positional.length
  let named := (args.keywords.map Prod.fst).zip afterPositional
  let expansions := afterPositional.drop args.keywords.length
  let star := if args.star.isSome then expansions[0]? else none
  let starStar := if args.starStar.isSome then expansions[args.star.toList.length]? else none
  let extraKeys ← expandStarStar starStar
  let extraValues ← expandStar star
  return ⟨positional ++ extraValues, named ++ extraKeys⟩

structure BoundArguments where
  named : List (Binding × Lists.Value)
  surplusPositional : List Lists.Value
  surplusKeywords : List (String × Lists.Value)

def bindKeyword (signature : Signature)
    (bound : List (Binding × Lists.Value) × List (String × Lists.Value))
    (actual : String × Lists.Value) :
    Except Error (List (Binding × Lists.Value) × List (String × Lists.Value)) :=
  let (name, value) := actual
  match signature.named.find? (fun p => p.slot.name == name) with
  | some parameter =>
    if (List.lookup parameter.slot bound.1).isSome then .error (.multipleArgumentValues name)
    else .ok ((parameter.slot, value) :: bound.1, bound.2)
  | none =>
    if signature.kwargs.isNone then .error (.unexpectedKeyword name)
    else if (List.lookup name bound.2).isSome then .error (.multipleArgumentValues name)
    else .ok (bound.1, bound.2 ++ [(name, value)])

/-- Bind without modifying the heap. Packs and activation slots are allocated
only after every required parameter is present. -/
def bindArguments (signature : Signature) (defaults : List (Binding × Lists.Value))
    (actual : Actual) : Except Error BoundArguments := do
  let parameters := signature.positional.map Parameter.slot
  let surplus := actual.positional.drop parameters.length
  if !surplus.isEmpty && signature.varargs.isNone then
    throw (.arity parameters.length actual.positional.length)
  let (named, extra) ← actual.keywords.foldlM (bindKeyword signature)
    (parameters.zip actual.positional, [])
  let filled := signature.named.map fun p =>
    (p.slot, (List.lookup p.slot named).orElse fun () => List.lookup p.slot defaults)
  let missing := filled.filterMap fun (slot, v) => if v.isNone then some slot.name else none
  if !missing.isEmpty then
    throw (.missingArguments missing)
  return ⟨filled.filterMap (fun (slot, v) => v.map fun value => (slot, value)), surplus, extra⟩

def packArgs (signature : Signature) (bound : BoundArguments) : Meaning (List (Binding × Lists.Value)) :=
  do
    let named ← match signature.varargs with
      | none => pure bound.named
      | some slot => do
        let tuple ← allocateTuple bound.surplusPositional
        pure ((slot, tuple) :: bound.named)
    match signature.kwargs with
    | none => pure named
    | some slot => do
      let dict ← allocateDict (bound.surplusKeywords.map fun (name, value) =>
        ⟨.string name, [.string name], value⟩)
      return (slot, dict) :: named

end Silmaril.Languages.Starlark.Functions
