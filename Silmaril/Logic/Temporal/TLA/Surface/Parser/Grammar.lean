module

public import Silmaril.Logic.Temporal.TLA.Surface.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Parser.Diagnostic
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Lexer
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Operators

namespace Silmaril.Logic.Temporal.TLA.Surface.Parser

private structure ParseState where
  tokens : Array Token
  offset : Nat := 0
  /-- An item of an active junction list can only consume tokens to its right. -/
  junctionColumn : Nat := 0
  /-- Numeric levels for hierarchy checks. The tree keeps the source's level markers. -/
  proofLevels : List Nat := []

private abbrev ParseM := StateT ParseState (Except Diagnostic)

private instance {α : Type} : Inhabited (ParseM α) :=
  ⟨throw ⟨.syntax, default, "parser did not run"⟩⟩

private def peek (ahead : Nat := 0) : ParseM Token := do
  let state ← get
  return state.tokens[state.offset + ahead]?.getD state.tokens.back!

private def failAt {α : Type} (token : Token) (message : String)
    (kind : DiagnosticKind := .syntax) : ParseM α :=
  throw ⟨kind, token.span, message⟩

private def failHere {α : Type} (message : String)
    (kind : DiagnosticKind := .syntax) : ParseM α := do
  failAt (← peek) message kind

private def inItem (token : Token) : ParseM Bool := do
  return token.span.start.column > (← get).junctionColumn

private def takeToken : ParseM Token := do
  let token ← peek
  if token.kind == .eof then failAt token "unexpected end of input"
  else if !(← inItem token) then failAt token "token is outside the active junction item"
  else
    modify fun state => { state with offset := state.offset + 1 }
    return token

private def Token.isOneOf (token : Token) (spellings : List String) : Bool :=
  token.kind != .string && spellings.contains token.text

private def Token.stepLabel (token : Token) : Option StepLabel := do
  match token.kind with
  | .step | .stepRef =>
    let [level, suffix] := token.text.splitOn ">" | none
    let level ← match level with
      | "<*" => some StepLevel.current
      | "<+" => some StepLevel.next
      | _ => (String.ofList (level.toList.drop 1)).toNat?.map .explicit
    let name := String.ofList (suffix.toList.takeWhile (fun c => c != '.' && c != '*' && c != '-'))
    return ⟨level, if name.isEmpty then none else some name⟩
  | _ => none

private def sees (spellings : List String) (ahead : Nat := 0) : ParseM Bool := do
  return (← peek ahead).isOneOf spellings

private def accept (spellings : List String) : ParseM Bool := do
  let token ← peek
  if token.isOneOf spellings && (← inItem token) then
    let _ ← takeToken
    return true
  return false

private def expectOne (spellings : List String) : ParseM Token := do
  let token ← peek
  if token.isOneOf spellings then takeToken
  else failAt token s!"expected {String.intercalate " or " spellings}"

private def expect (spelling : String) : ParseM Unit := do
  let _ ← expectOne [spelling]

private def ident : ParseM Ident := do
  let token ← peek
  if token.kind == .ident then return (← takeToken).text
  failAt token "expected an identifier"

-- JavaCC permits these reserved words in selected field and module-name positions.
private def Token.isFieldName (token : Token) : Bool :=
  token.kind == .ident || token.kind == .keyword || token.isOneOf ["[]ASSUME", "[]PROVE", "_"]

private def fieldName : ParseM Ident := do
  let token ← peek
  if token.isFieldName then return (← takeToken).text
  failAt token "expected a field or module name"

private def commaTail {α : Type} (first : α) (item : ParseM α) : ParseM (List α) := do
  let mut items := [first]
  while ← accept [","] do
    items := (← item) :: items
  return items.reverse

private def commaList {α : Type} (item : ParseM α) : ParseM (List α) := do
  commaTail (← item) item

private def delimited {α : Type} (close : List String) (body : ParseM α) : ParseM α := do
  let result ← body
  let _ ← expectOne close
  return result

private def Token.operator (token : Token) : Option Operator :=
  if token.kind == .symbol || token.kind == .keyword then lookupOperator token.text else none

private def Token.prefix (token : Token) : Option Operator :=
  -- A leading "-" is mixfix. The literal "-." is its symbolic name.
  if token.isOneOf ["-"] then lookupOperator "-."
  else token.operator.filter (fun op => op.fixity == .prefix && op.canonical != "-.")

private def Token.infix (token : Token) : Option Operator :=
  if token.isOneOf ["."] then none
  else token.operator.filter (fun op => op.fixity == .infix || op.fixity == .product)

private def Token.postfix (token : Token) : Option Operator :=
  if token.isOneOf ["["] then none
  else token.operator.filter (·.fixity == .postfix)

private def Token.junction (token : Token) : Option Junction :=
  if token.isOneOf ["/\\", "∧"] then some .conjunction
  else if token.isOneOf ["\\/", "∨"] then some .disjunction
  else none

private def junctionMarkers : Junction → List String
  | .conjunction => ["/\\", "∧"]
  | .disjunction => ["\\/", "∨"]

private def symbolOf (token : Token) (op : Operator) : Option Symbol :=
  match op.fixity with
  | .prefix => some (.prefix (op.prefixOp token.text))
  | .infix => if token.isOneOf ["."] then none else some (.infix (op.infixOp token.text))
  | .postfix => if token.isOneOf ["["] then none else some (.postfix (op.postfixOp token.text))
  | .product => some (.infix (.symbol token.text))

-- Prefix operators whose names can appear in declarations and as operator arguments.
private def Token.isNamedPrefix (token : Token) : Bool :=
  token.operator.any (·.fixity == .prefix)

private def operatorName : ParseM OperatorName := do
  let token ← peek
  if token.kind == .ident then return .ident (← ident)
  let some op := token.operator | failAt token "expected an operator name"
  let some symbol := symbolOf token op | failAt token "expected a named operator"
  let _ ← takeToken
  return .symbolic symbol

private def visibility : ParseM Visibility := do
  return if ← accept ["LOCAL"] then .local else .ordinary

private def operatorDecl : ParseM OperatorDecl := do
  let token ← peek
  if token.kind == .ident then
    let name ← ident
    let arity ← if ← accept ["("] then
      pure (← delimited [")"] (commaList (expect "_"))).length
    else pure 0
    return .ident name arity
  let left ← accept ["_"]
  let token ← peek
  let some op := token.operator | failAt token "expected an operator declaration"
  let some symbol := symbolOf token op | failAt token "expected a declarable operator"
  match symbol with
  | .prefix _ =>
    if left || !token.isNamedPrefix then failAt token "expected a declarable prefix operator"
    let _ ← takeToken
    expect "_"
  | .infix _ =>
    if !left then failAt token "expected _ before an infix operator declaration"
    let _ ← takeToken
    expect "_"
  | .postfix _ =>
    if !left then failAt token "expected _ before a postfix operator declaration"
    let _ ← takeToken
  return .symbolic symbol

private def numberValue (text : String) : Nat :=
  let digit (c : Char) :=
    if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  match text.toList with
  | '\\' :: tag :: digits =>
    let base := if tag.toLower == 'h' then 16 else if tag.toLower == 'o' then 8 else 2
    digits.foldl (fun value c => value * base + digit c) 0
  | _ => text.toNat?.getD 0

private def nameListEnd (first : Nat) : ParseM Nat := do
  let mut offset := first
  if (← peek offset).kind != .ident then return offset
  offset := offset + 1
  while (← sees [","] offset) && (← peek (offset + 1)).kind == .ident do
    offset := offset + 2
  return offset

/-- Look ahead through a paired delimiter without consuming it. The caller has
already found the opener at the supplied offset. -/
private def afterDelimiter (offset : Nat) (openers closers : List String) :
    ParseM (Option Nat) := do
  let mut depth := 1
  let mut next := offset + 1
  while depth > 0 do
    let token ← peek next
    if token.kind == .eof || token.kind == .endModule then return none
    if token.isOneOf openers then depth := depth + 1
    if token.isOneOf closers then depth := depth - 1
    next := next + 1
  return some next

private def membership := ["\\in", "∈"]
private def definitionMark := ["==", "≜"]

-- Recognize SANY's synthetic DEFBREAK boundary without inserting tokens.
private def startsDefinition (ahead : Nat := 0) : ParseM Bool := do
  let token ← peek ahead
  if token.isOneOf ["-|-"] then return true
  let next ← peek (ahead + 1)
  if token.kind != .ident then
    return token.isNamedPrefix && next.kind == .ident && (← sees definitionMark (ahead + 2))
  if next.isOneOf definitionMark then return true
  if next.postfix.isSome then return ← sees definitionMark (ahead + 2)
  if next.infix.isSome then
    return (← peek (ahead + 2)).kind == .ident && (← sees definitionMark (ahead + 3))
  let after ← if next.isOneOf ["("] then afterDelimiter (ahead + 1) ["("] [")"]
    else if next.isOneOf ["["] then afterDelimiter (ahead + 1) ["["] ["]", "]_"]
    else pure none
  if let some offset := after then return ← sees definitionMark offset
  return false

private def startsBound : ParseM Bool := do
  -- SANY's matchFcnConst commits on a tuple followed by membership.
  -- The tuple's contents are checked later by IdentifierTuple.
  if ← sees ["<<", "⟨"] then
    if let some offset ← afterDelimiter 0 ["<<", "⟨"] [">>", "⟩"] then
      return ← sees membership offset
    return false
  if (← peek).kind == .ident then return ← sees membership (← nameListEnd 0)
  return false

private def tupleNames : ParseM (List Ident) := do
  let _ ← expectOne ["<<", "⟨"]
  if ← accept [">>", "⟩"] then return []
  delimited [">>", "⟩"] (commaList ident)

private def pattern : ParseM BoundPattern := do
  if ← sees ["<<", "⟨"] then return .tuple (← tupleNames)
  return .ident (← ident)

private def patternExpr : BoundPattern → Expr
  | .ident name => .ref (.operator (.ident name)) [] []
  | .tuple names => .tuple (names.map fun name => .ref (.operator (.ident name)) [] [])

private structure Pending where
  token : Token
  op : Operator

/-- Compare with the operator waiting for an operand. Overlapping ranges only
allow a left reduction for the same left-associative infix (or product). -/
private def bindsInside (parent : Option Pending) (next : Pending) : ParseM Bool := do
  let some left := parent | return true
  if left.op.high < next.op.low then return true
  if next.op.high < left.op.low ||
      (left.op.canonical == next.op.canonical && left.op.leftAssociative) then return false
  failAt next.token s!"precedence conflict between {left.token.text} and {next.token.text}. Use parentheses"
    .precedence

-- Delay construction of a product until the chain ends. A parenthesized
-- product enters the enclosing parse as an ordinary expression.
private inductive ParsedExpr where
  | single (value : Expr)
  | product (reversedFactors : List Expr)
  deriving Inhabited

private def ParsedExpr.finish : ParsedExpr → Expr
  | .single value => value
  | .product factors => .cartesian factors.reverse

private def ParsedExpr.appendFactor (left : ParsedExpr) (right : Expr) : ParsedExpr :=
  match left with
  | .single value => .product [right, value]
  | .product factors => .product (right :: factors)

private def labelEnd : ParseM (Option Nat) := do
  if (← peek).kind != .ident then return none
  if ← sees ["::", "∷"] 1 then return some 1
  if ← sees ["("] 1 then
    let offset ← nameListEnd 2
    if (← peek 2).kind == .ident && (← sees [")"] offset) && (← sees ["::", "∷"] (offset + 1)) then
      return some (offset + 1)
  return none

private def stopsBareOperator (token : Token) : Bool :=
  token.kind == .beginModule || token.kind == .endModule || token.kind == .separator ||
    token.isOneOf [",", ")", "LOCAL", "INSTANCE", "THEOREM", "ASSUME", "ASSUMPTION", "AXIOM",
      "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES", "RECURSIVE", "IN"]

-- Each recursive expression call either consumes an opener/operator or returns
-- to its caller at a delimiter or weaker operator.
mutual

private partial def expression : ParseM Expr := do
  return (← operand none).finish

private partial def operand (parent : Option Pending) : ParseM ParsedExpr := do
  let token ← peek
  if !(← inItem token) then failAt token "expected an expression to the right of the junction marker"
  else if let some op := token.prefix then
    if token.text == "-" then
      if let some left := parent then
        -- SANY's mixfix '-' cannot follow an already stronger pending operator.
        if left.op.low > op.high then
          failAt token s!"precedence conflict between {left.token.text} and unary -. Use parentheses"
            .precedence
    let _ ← takeToken
    let value ← operand (some ⟨token, op⟩)
    extend parent (.single (.prefix (op.prefixOp token.text) value.finish))
  else if let some _ ← labelEnd then
    let name ← ident
    let parameters ← if ← accept ["("] then delimited [")"] (commaList ident) else pure []
    let _ ← expectOne ["::", "∷"]
    let start ← peek
    let body ← expression
    if let some left := parent then
      -- A label cannot change the binding of the operator at the root of its body.
      -- Parenthesized bodies have their own precedence context.
      if !start.isOneOf ["("] then
        let root := match body with
          | .infix (.symbol spelling) .. => lookupOperator spelling
          | .infix .compose .. => lookupOperator "\\cdot"
          | .infix .leadsTo .. => lookupOperator "~>"
          | .infix .guarantees .. => lookupOperator "-+->"
          | .postfix .prime _ => lookupOperator "'"
          | .postfix (.symbol spelling) _ => lookupOperator spelling
          | _ => none
        if let some op := root then
          if left.op.high ≥ op.low then failAt start "label changes operator grouping. Use parentheses"
    return .single (.labeled ⟨name, parameters⟩ body)
  else if token.isOneOf ["IF", "CASE", "LET", "CHOOSE", "\\A", "\\forall", "∀",
      "\\E", "\\exists", "∃", "\\AA", "\\EE"] then
    return .single (← openExpression)
  else
    extend parent (.single (← atom))

private partial def extend (parent : Option Pending) (left : ParsedExpr) : ParseM ParsedExpr := do
  let next ← peek
  if !(← inItem next) then return left
  if next.isOneOf ["."] then
    let _ ← takeToken
    extend parent (.single (.field left.finish (← fieldName)))
  else if next.isOneOf ["["] then
    let _ ← takeToken
    if ← startsBound then failHere "parenthesize a membership expression used as an index"
    let args ← delimited ["]"] (commaList expression)
    extend parent (.single (.index left.finish args))
  else if let some op := next.postfix then
    if !(← bindsInside parent ⟨next, op⟩) then return left
    let _ ← takeToken
    extend parent (.single (.postfix (op.postfixOp next.text) left.finish))
  else if let some op := next.infix then
    if !(← bindsInside parent ⟨next, op⟩) then return left
    let _ ← takeToken
    let right := (← operand (some ⟨next, op⟩)).finish
    let result := if op.fixity == .product then left.appendFactor right
      else .single (.infix (op.infixOp next.text) left.finish right)
    extend parent result
  else if next.isOneOf ["::", "∷"] then
    failAt next "only identifier labels with identifier parameters are supported" .unsupported
  else
    return left

private partial def atom : ParseM Expr := do
  let token ← peek
  if let some kind := token.junction then junction kind token.span.start.column
  else if token.kind == .number then
    let _ ← takeToken
    if (← sees ["."]) && (← peek 1).kind == .number then
      let _ ← takeToken
      let fraction ← takeToken
      if token.text.startsWith "\\" || fraction.text.startsWith "\\" then
        failAt token "base-prefixed decimal pieces are unsupported" .unsupported
      return .literal (.decimal (numberValue token.text) fraction.text)
    return .literal (.natural (numberValue token.text))
  else if token.kind == .string then
    return .literal (.string (← takeToken).text)
  else if token.kind == .ident || token.kind == .stepRef ||
      (token.operator.isSome && !token.isOneOf ["[", "."]) then
    reference false
  else if token.isOneOf ["WF_", "SF_"] then
    let _ ← takeToken
    fairness (if token.text == "WF_" then .weak else .strong)
  else reduced

private partial def reference (restricted : Bool) : ParseM Expr := do
  let head ← if restricted then pure (.operator (.ident (← ident))) else referenceHead
  let args ← refArgs
  let mut selectors := []
  while ← accept ["!"] do
    selectors := (← if restricted then do
      let name ← ident
      pure (.named (.ident name) (← refArgs))
    else selector) :: selectors
  if let .operator (.ident "@") := head then
    if args.isEmpty && selectors.isEmpty then return .oldValue
  return .ref head args selectors.reverse

private partial def referenceHead : ParseM RefHead := do
  let token ← peek
  if token.kind != .stepRef then return .operator (← operatorName)
  if (← get).proofLevels.isEmpty then failAt token "proof-step reference outside a hierarchical proof"
  let some ⟨level, some name⟩ := token.stepLabel | failAt token "expected a named proof-step reference"
  let level ← match level with
    | .explicit n => pure (StepRefLevel.explicit n)
    | .current => pure .current
    | .next => failAt token "<+> cannot be used in a proof-step reference"
  let _ ← takeToken
  return .step ⟨level, name⟩

private partial def reduced : ParseM Expr := do
  let token ← peek
  if token.kind == .ident then return ← reference true
  if ← accept ["("] then return ← delimited [")"] expression
  if ← accept ["{"] then return ← brace
  if ← accept ["["] then return ← bracket
  if ← accept ["<<", "⟨"] then
    if ← accept [">>", "⟩"] then return .tuple []
    if ← sees [">>_", "⟩_"] then
      failAt token "angle action must have a single body" .unsupported
    let elements ← commaList expression
    if ← accept [">>_", "⟩_"] then
      if let [body] := elements then return .action .angle body (← reduced)
      failAt token "angle action must have a single body" .unsupported
    else
      let _ ← expectOne [">>", "⟩"]
      return .tuple elements
  failAt token "expected a TLA+ expression"

private partial def refArgs : ParseM (List OpArg) := do
  if ← accept ["("] then delimited [")"] (commaList opArg)
  else pure []

private partial def opArg : ParseM OpArg := do
  let token ← peek
  if ← accept ["LAMBDA"] then
    let parameters ← commaList ident
    expect ":"
    return .lambda parameters (← expression)
  if let some op := token.operator then
    if stopsBareOperator (← peek 1) || (← startsDefinition 1) then
      if op.fixity == .product then failAt token "a Cartesian product cannot be a bare operator argument"
      let some symbol := symbolOf token op | failAt token "expected a standalone operator"
      let _ ← takeToken
      return .symbolic symbol
  return .expr (← expression)

private partial def selector : ParseM Selector := do
  let token ← peek
  if ← sees ["("] then return .arguments (← refArgs)
  if token.kind == .number then
    let _ ← takeToken
    if (← sees ["."]) && (← peek 1).kind == .number then
      failAt token "a structural selector must be a natural numeral"
    return .structural (.operand (numberValue token.text))
  if ← accept ["<<", "⟨"] then return .structural .left
  if ← accept [">>", "⟩"] then return .structural .right
  if ← accept [":"] then return .structural .body
  if ← accept ["@"] then return .structural .allBindings
  let name ← operatorName
  return .named name (← refArgs)

private partial def junction (kind : Junction) (column : Nat) : ParseM Expr := do
  let outer := (← get).junctionColumn
  let mut items := []
  repeat
    let _ ← expectOne (junctionMarkers kind)
    modify fun state => { state with junctionColumn := column }
    items := (← expression) :: items
    modify fun state => { state with junctionColumn := outer }
    let next ← peek
    if next.span.start.column != column || !next.isOneOf (junctionMarkers kind) then break
  return .junction kind items.reverse

private partial def bound : ParseM Bound := do
  let names ← if ← sees ["<<", "⟨"] then
    pure (.tuple (← tupleNames))
  else
    pure (.names (← commaList ident))
  let _ ← expectOne membership
  return ⟨names, ← expression⟩

private partial def rigidBinders : ParseM RigidBinders := do
  if ← startsBound then return .bounded (← commaList bound)
  return .unbounded (← commaList ident)

private partial def brace : ParseM Expr := do
  if ← accept ["}"] then return .setEnum []
  if ← startsBound then
    let binder ← pattern
    let member ← expectOne membership
    let domain ← expression
    if ← accept [":"] then return .setFilter binder domain (← delimited ["}"] expression)
    let first := Expr.infix (.symbol member.text) (patternExpr binder) domain
    return .setEnum (← delimited ["}"] (commaTail first expression))
  let start := (← get).offset
  let startsParens ← sees ["("]
  let body ← expression
  let stop := (← get).offset
  if ← accept [":"] then
    if let .infix (.symbol "\\in") _ _ := body then
      -- This JavaCC alternative rejects an ungrouped ASCII membership
      -- expression as the result of a set map.
      let wrapped ← if startsParens then
        -- Use the original offset for lookahead because expression has advanced.
        let state ← get
        set { state with offset := start }
        let after ← afterDelimiter 0 ["("] [")"]
        set state
        pure (after == some (stop - start))
      else pure false
      if !wrapped then failHere "parenthesize a membership expression used as the result of a set map"
    return .setMap body (← delimited ["}"] (commaList bound))
  return .setEnum (← delimited ["}"] (commaTail body expression))

private partial def fieldEntry (marker : List String) (nameParser : ParseM Ident) : ParseM Field := do
  let name ← nameParser
  let _ ← expectOne marker
  return ⟨name, ← expression⟩

private partial def bracket : ParseM Expr := do
  if ← startsBound then
    let bounds ← commaList bound
    let _ ← expectOne ["|->", "↦"]
    return .function bounds (← delimited ["]"] expression)
  if (← peek).isFieldName && (← sees ["|->", "↦"] 1) then
    let first ← fieldEntry ["|->", "↦"] fieldName
    return .record (← delimited ["]"] (commaTail first (fieldEntry ["|->", "↦"] ident)))
  if (← peek).kind == .ident && (← sees [":"] 1) then
    return .recordSet (← delimited ["]"] (commaList (fieldEntry [":"] ident)))
  let base ← expression
  if ← accept ["->", "→"] then return .functionSet base (← delimited ["]"] expression)
  if ← accept ["EXCEPT"] then return .except base (← delimited ["]"] (commaList update))
  if ← accept ["]_"] then return .action .square base (← reduced)
  if ← sees [",", "]"] then
    let token ← peek
    let _ ← delimited ["]"] (commaTail base expression)
    failAt token "a bare index payload has no function to index" .unsupported
  failHere "expected ->, EXCEPT, or ]_ in a bracket expression"

private partial def update : ParseM Update := do
  expect "!"
  let mut path := []
  repeat
    if ← accept ["."] then
      if ← sees ["@"] then failHere "@ is invalid as an EXCEPT field name"
      path := .field (← fieldName) :: path
    else if ← accept ["["] then
      path := .index (← delimited ["]"] (commaList expression)) :: path
    else break
  if path.isEmpty then failHere "expected a field or index in an EXCEPT path"
  expect "="
  return ⟨path.reverse, ← expression⟩

private partial def fairness (kind : Fairness) : ParseM Expr := do
  let namedObservation := (← peek).kind == .ident
  let observation ← reduced
  if ← accept ["("] then return .fairness kind observation (← delimited [")"] expression)
  -- An unparenthesized reference consumes its argument list before we can
  -- tell whether it is the observation's argument list or the fairness action.
  if namedObservation then
    if let .ref head args selectors := observation then
      match selectors.reverse with
      | .named name [.expr action] :: rest =>
        return .fairness kind (.ref head args ((.named name [] :: rest).reverse)) action
      | [] =>
        if let [.expr action] := args then return .fairness kind (.ref head [] []) action
      | _ => pure ()
  failHere "expected a single fairness action in parentheses"

private partial def openExpression : ParseM Expr := do
  let token ← takeToken
  if token.text == "IF" then
    let condition ← expression
    expect "THEN"
    let consequent ← expression
    expect "ELSE"
    return .ifThenElse condition consequent (← expression)
  if token.text == "LET" then
    let mut declarations := []
    repeat
      let declaration ← if ← accept ["RECURSIVE"] then
        pure (.recursive (← commaList operatorDecl))
      else
        pure (.definition (← definition (← visibility)))
      declarations := declaration :: declarations
      if ← accept ["IN"] then break
    return .letIn declarations.reverse (← expression)
  if token.text == "CASE" then
    let mut arms := [← caseArm]
    while ← accept ["[]", "□"] do
      if ← accept ["OTHER"] then
        let _ ← expectOne ["->", "→"]
        return .cases arms.reverse (some (← expression))
      arms := (← caseArm) :: arms
    return .cases arms.reverse none
  if token.text == "CHOOSE" then
    let binder ← pattern
    let domain ← if ← accept membership then
      pure (some (← expression))
    else pure none
    expect ":"
    return .choose binder domain (← expression)
  let quantifier := if token.isOneOf ["\\A", "\\forall", "∀", "\\AA"] then
    Quantifier.forall else .exists
  if token.isOneOf ["\\AA", "\\EE"] then
    let names ← commaList ident
    expect ":"
    return .temporalQuant quantifier names (← expression)
  let binders ← rigidBinders
  expect ":"
  return .rigidQuant quantifier binders (← expression)

private partial def caseArm : ParseM CaseArm := do
  let condition ← expression
  let _ ← expectOne ["->", "→"]
  return ⟨condition, ← expression⟩

private partial def definition (vis : Visibility) : ParseM Definition := do
  let _ ← accept ["-|-"]
  let token ← peek
  if token.kind == .ident then
    let name ← ident
    if ← accept ["["] then
      let bounds ← delimited ["]"] (commaList bound)
      let _ ← expectOne definitionMark
      return .function vis name bounds (← expression)
    let operator ← peek
    if let some op := operator.postfix then
      let _ ← takeToken
      let _ ← expectOne definitionMark
      return .operator vis (.postfix name (op.postfixOp operator.text)) (← expression)
    if let some op := operator.infix then
      let _ ← takeToken
      let right ← ident
      let _ ← expectOne definitionMark
      return .operator vis (.infix name (op.infixOp operator.text) right) (← expression)
    let params ← if ← accept ["("] then delimited [")"] (commaList operatorDecl) else pure []
    let _ ← expectOne definitionMark
    if ← sees ["INSTANCE"] then return .namedInstance vis name params (← instantiation)
    return .operator vis (.ident name params) (← expression)
  if token.isNamedPrefix then
    let some op := token.operator | failAt token "expected a prefix operator"
    let _ ← takeToken
    let name ← ident
    let _ ← expectOne definitionMark
    return .operator vis (.prefix (op.prefixOp token.text) name) (← expression)
  failAt token "expected a definition"

private partial def instantiation : ParseM Instantiation := do
  expect "INSTANCE"
  let name ← fieldName
  let substitutions ← if ← accept ["WITH"] then commaList substitution else pure []
  return ⟨name, substitutions⟩

private partial def substitution : ParseM Substitution := do
  let target ← operatorName
  let _ ← expectOne ["<-", "←"]
  return ⟨target, ← opArg⟩

end

private def optionalName : ParseM (Option Ident) := do
  if (← peek).kind == .ident && (← sees definitionMark 1) then
    let name ← ident
    let _ ← expectOne definitionMark
    return some name
  return none

private def assumptionMark := ["ASSUME", "[]ASSUME"]

private def assumeMode (token : Token) : AssumeProveMode :=
  if token.text.startsWith "[]" then .boxed else .plain

mutual

private partial def statement (allowLabel : Bool := false) : ParseM Statement := do
  if allowLabel && (← peek).kind == .ident &&
      (← sees ["::", "∷"] 1) && (← sees assumptionMark 2) then
    let name ← ident
    let _ ← expectOne ["::", "∷"]
    return .labeled name (← statement)
  if ← sees assumptionMark then
    let mode := assumeMode (← takeToken)
    let hypotheses ← commaList hypothesis
    let goalMode := assumeMode (← expectOne ["PROVE", "[]PROVE"])
    return .assumeProve mode hypotheses goalMode (← expression)
  return .expr (← expression)

private partial def hypothesis : ParseM Hypothesis := do
  if !(← sees ["NEW", "VARIABLE", "VARIABLES", "CONSTANT", "CONSTANTS", "STATE",
    "ACTION", "ACTIONS", "TEMPORAL", "TEMPORALS"]) then
    return .statement (← statement true)
  let _ ← accept ["NEW"]
  if ← accept ["VARIABLE", "VARIABLES"] then return .newVariable (← ident)
  let level ← if ← accept ["STATE"] then pure .state
    else if ← accept ["ACTION", "ACTIONS"] then pure .action
    else if ← accept ["TEMPORAL", "TEMPORALS"] then pure .temporal
    else
      let _ ← accept ["CONSTANT", "CONSTANTS"]
      pure .constant
  let declaration ← operatorDecl
  if let .constant := level then
    if ← accept membership then
      if let .ident name 0 := declaration then return .newBoundConstant name (← expression)
      failHere "a bounded constant must have arity zero"
  return .newSymbol level declaration

end

private def citation : ParseM Citation := do
  if ← accept ["MODULE"] then return .moduleName (← ident)
  return .expr (← expression)

private def startsCitation : ParseM Bool := do
  let token ← peek
  return token.kind == .ident || token.kind == .number || token.kind == .string ||
    token.kind == .stepRef || (token.operator.isSome && !token.isOneOf ["."]) ||
    token.isOneOf ["MODULE", "(", "[", "{", "<<", "⟨", "@", "WF_", "SF_", "IF", "CASE",
      "LET", "CHOOSE", "\\A", "\\forall", "∀", "\\E", "\\exists", "∃", "\\AA", "\\EE"]

private def citations : ParseM Citations := do
  let facts ← if (← startsCitation) && !(← startsDefinition) then commaList citation else pure []
  let defs ← if ← accept ["DEF", "DEFS"] then commaList citation else pure []
  return ⟨facts, defs⟩

private def startsProof : ParseM Bool := do
  let token ← peek
  if token.isOneOf ["PROOF", "OBVIOUS", "OMITTED", "BY"] then return true
  let parent := (← get).proofLevels.head?
  match token.stepLabel with
  | some ⟨.current, _⟩ => return parent.isNone
  | some ⟨.next, _⟩ => return true
  | some ⟨.explicit level, _⟩ => return parent.all (· < level)
  | none => return false

private def stepDefinitions : ParseM (List Definition) := do
  let mut definitions := [← definition (← visibility)]
  while ← startsDefinition (if ← sees ["LOCAL"] then 1 else 0) do
    definitions := (← definition (← visibility)) :: definitions
  return definitions.reverse

mutual

private partial def proof : ParseM (Option Proof) := do
  if !(← startsProof) then return none
  let parents := (← get).proofLevels
  if parents.length ≥ 100 then failHere "proofs nested more than 100 deep"
  let _ ← accept ["PROOF"]
  if ← accept ["OBVIOUS"] then return some .obvious
  if ← accept ["OMITTED"] then return some .omitted
  if ← accept ["BY"] then return some (.byFacts (← accept ["ONLY"]) (← citations))
  let token ← peek
  let some first := token.stepLabel | failAt token "expected a proof step header"
  let level ← match first.level with
    | .explicit level =>
      if parents.head?.any (· ≥ level) then failAt token "nested proof level must exceed its parent"
      pure level
    | .current | .next => pure (parents.head?.map (· + 1) |>.getD 0)
  modify fun state => { state with proofLevels := level :: parents }
  let result ← proofSteps level
  modify fun state => { state with proofLevels := parents }
  return some result

private partial def proofSteps (level : Nat) : ParseM Proof := do
  let mut first := true
  let mut steps := []
  repeat
    let token ← peek
    let some label := token.stepLabel | failAt token "expected a proof step header or labeled QED"
    let sameLevel := match label.level with
      | .explicit n => n == level
      | .current => true
      | .next => first
    if !sameLevel then failAt token "proof step level does not match its siblings"
    let _ ← takeToken
    if ← accept ["QED"] then return .steps steps.reverse label (← proof)
    steps := ⟨label, ← stepBody⟩ :: steps
    first := false

private partial def stepBody : ParseM StepBody := do
  if ← accept ["PICK"] then
    let binders ← rigidBinders
    expect ":"
    return .pick binders (← expression) (← proof)
  if ← accept ["CASE"] then return .caseOf (← expression) (← proof)
  if ← accept ["SUFFICES"] then return .suffices (← statement) (← proof)
  let body ← if ← accept ["USE"] then
    pure (.directive (.use (← accept ["ONLY"]) (← citations)))
  else if ← accept ["HIDE"] then pure (.directive (.hide (← citations)))
  else if ← sees ["INSTANCE"] then pure (.instantiation (← instantiation))
  else if (← accept ["DEFINE"]) || (← startsDefinition) then pure (.define (← stepDefinitions))
  else if ← accept ["HAVE"] then pure (.have (← expression))
  else if ← accept ["TAKE"] then pure (.take (← rigidBinders))
  else if ← accept ["WITNESS"] then pure (.witness (← commaList expression))
  else return .assert (← statement) (← proof)
  if ← startsProof then failHere "this kind of proof step cannot have a proof"
  return body

end

private partial def moduleBody : ParseM Module := do
  let token ← peek
  if token.kind != .beginModule then failAt token "expected a module header (---- MODULE)"
  let _ ← takeToken
  let name ← fieldName
  let separator ← peek
  if separator.kind != .separator then failAt separator "expected at least four dashes after module name"
  let _ ← takeToken
  let extendsModules ← if ← accept ["EXTENDS"] then commaList fieldName else pure []
  let mut units := []
  repeat
    let token ← peek
    if token.kind == .endModule then
      let _ ← takeToken
      return ⟨name, extendsModules, units.reverse⟩
    if token.kind == .eof then failAt token "expected a module terminator (====)"
    if token.kind == .separator then
      let _ ← takeToken
      continue
    let unit ← if token.kind == .beginModule then
      pure (.submodule (← moduleBody))
    else if ← accept ["VARIABLE", "VARIABLES"] then
      pure (.variables (← commaList ident))
    else if ← accept ["CONSTANT", "CONSTANTS"] then
      pure (.constants (← commaList operatorDecl))
    else if ← accept ["RECURSIVE"] then
      pure (.recursive (← commaList operatorDecl))
    else if ← accept ["ASSUME", "ASSUMPTION", "AXIOM"] then
      pure (.assumption (← optionalName) (← expression))
    else if ← accept ["THEOREM", "PROPOSITION", "LEMMA", "COROLLARY"] then
      pure (.theoremDecl ⟨← optionalName, ← statement, ← proof⟩)
    else if ← accept ["USE"] then
      pure (.directive (.use false (← citations)))
    else if ← accept ["HIDE"] then
      pure (.directive (.hide (← citations)))
    else
      let vis ← visibility
      if ← sees ["INSTANCE"] then pure (.instantiation vis (← instantiation))
      else pure (.definition (← definition vis))
    units := unit :: units

private def wholeSource {α : Type} (parser : ParseM α) (source : String) : Except Diagnostic α := do
  let tokens ← tokenize source
  let parse : ParseM α := do
    let result ← parser
    let token ← peek
    if token.kind != .eof then failAt token "unexpected token after complete input"
    return result
  return (← parse.run { tokens }).1

public def readModule (source : String) : Except Diagnostic Module :=
  wholeSource (do
    if ← sees ["--->"] then failHere "a SANY prelude pragma is unsupported" .unsupported
    moduleBody) source

public def readExpr (source : String) : Except Diagnostic Expr :=
  wholeSource expression source

end Silmaril.Logic.Temporal.TLA.Surface.Parser
