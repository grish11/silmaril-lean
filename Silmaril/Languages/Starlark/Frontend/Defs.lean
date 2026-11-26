module

public import Silmaril.Languages.Starlark.Defs
public import Silmaril.Languages.Starlark.Frontend.Lexer.Defs

/-! # Scalar Starlark source text

See `docs/projects/starlark-frontend.md` for the admitted grammar and diagnostics.
Resolution and denotation operate on the lowered `SourceStmt`.
-/

public section

namespace Silmaril.Languages.Starlark.Frontend

structure LocatedStmt (Stmt : Type := SourceStmt) where
  span : Span
  stmt : Stmt

structure ParsedModule where
  statements : List LocatedStmt

/-- A standalone scalar function whose body can be passed to `runFunctionBody`. -/
structure ParsedFunction where
  name : String
  parameters : List String
  span : Span
  body : List LocatedStmt

structure LocatedArgument where
  span : Span
  expr : SourceExpr

structure LocatedParameter where
  span : Span
  name : String
  defaultValue : Option LocatedArgument

structure LocatedFunction (Stmt : Type := SourceStmt) where
  name : String
  parameters : List LocatedParameter
  span : Span
  body : List (LocatedStmt Stmt)

structure LocatedNamedArgument (Operand : Type := LocatedArgument) where
  nameSpan : Span
  name : String
  value : Operand

inductive CollectionDisplay where
  | sequence (isTuple : Bool) (elements : List LocatedArgument)
  | mapping (entries : List LocatedNamedArgument)

structure LocatedSpread (Operand : Type) where
  span : Span
  operand : Operand

/-- Groups in the source order prescribed by Starlark. -/
structure CallArguments (Operand : Type) where
  positional : List Operand := []
  named : List (LocatedNamedArgument Operand) := []
  star : Option (LocatedSpread Operand) := none
  starStar : Option (LocatedSpread Operand) := none

structure LocatedString where
  span : Span
  text : String

/-- Source expressions used within module call assignments. -/
inductive CallOperand where
  | scalar (value : LocatedArgument)
  | display (span : Span) (display : CollectionDisplay)
  | call (span : Span) (callee : CallOperand) (arguments : CallArguments CallOperand)

abbrev LocatedCallArguments := CallArguments CallOperand

def CallOperand.span : CallOperand → Span
  | .scalar value => value.span
  | .display span _ | .call span .. => span

structure CallSpans where
  positional : List Span
  named : List (String × Span)
  star : Option Span
  starStar : Option Span

/-- Operand spans, in evaluation order, starting after the callee. -/
def CallSpans.ordered (spans : CallSpans) : List Span :=
  spans.positional ++ spans.named.map Prod.snd ++ spans.star.toList ++ spans.starStar.toList

/-- Named and spread spans include their argument introducers. -/
@[expose] def LocatedCallArguments.spans (arguments : LocatedCallArguments) : CallSpans :=
  ⟨arguments.positional.map CallOperand.span,
    arguments.named.map (fun item => (item.name, ⟨item.nameSpan.start, item.value.span.stop⟩)),
    arguments.star.map LocatedSpread.span, arguments.starStar.map LocatedSpread.span⟩

structure LocatedImport where
  exported : LocatedString
  localName : LocatedString

/-- Module function suites retain the call expression at a return site. -/
inductive FunctionStmt where
  | scalar (stmt : SourceStmt)
  | returnCall (value : CallOperand)
  | branch (test : SourceExpr) (yes no : List (LocatedStmt FunctionStmt))

/-- The source forms consumed by the normalized module adapter. -/
inductive FileCommand where
  | simple (stmt : SourceStmt)
  | define (fn : LocatedFunction FunctionStmt)
  | assignDisplay (target : String) (display : CollectionDisplay)
  | assignCall (target : String) (value : CallOperand)
  | load (label : LocatedString) (imports : List LocatedImport)

structure LocatedFileCommand where
  span : Span
  command : FileCommand

private def sequence (statements : List LocatedStmt) : SourceStmt :=
  match statements.reverse with
  | [] => .pass
  | last :: preceding => preceding.foldl (fun rest first => .seq first.stmt rest) last.stmt

/-- Erase statement locations and compose the existing scalar AST in source order. -/
def ParsedModule.toSourceStmt (parsed : ParsedModule) : SourceStmt := sequence parsed.statements

/-- Lower the body in its function context, with parameters bound by the caller. -/
def ParsedFunction.toSourceStmt (parsed : ParsedFunction) : SourceStmt := sequence parsed.body

private structure Stream where
  remaining : List Token
  lastEnd : Position := {}

private def Stream.peek (s : Stream) : Token :=
  s.remaining.headD ⟨.eof, ⟨s.lastEnd, s.lastEnd⟩⟩

private def Stream.pop (s : Stream) : Stream :=
  let stop := match s.peek.kind with
    | .newline | .indent | .outdent | .eof => s.lastEnd
    | _ => s.peek.span.stop
  ⟨s.remaining.drop 1, stop⟩

private def failAt {α : Type} (kind : DiagnosticKind) (s : Stream) : Except Diagnostic α :=
  .error ⟨kind, s.peek.span⟩

private def expect {α : Type} (description : String) (s : Stream) : Except Diagnostic α :=
  failAt (.expected description) s

private inductive Infix where
  | arithmetic (priority : Nat) (op : BinaryOp)
  | comparison (op : Option BinaryOp)
  | logical (op : LogicalOp)

private def Infix.priority : Infix → Nat
  | .logical .or => 1
  | .logical .and => 2
  | .comparison _ => 4
  | .arithmetic p _ => p

private def infixOperator (s : Stream) : Option Infix :=
  match s.peek.kind with
  | .keyword "or" => some (.logical .or)
  | .keyword "and" => some (.logical .and)
  | .keyword "in" => some (.comparison none)
  | .keyword "not" =>
    if s.pop.peek.kind = .keyword "in" then some (.comparison none) else none
  | .symbol "==" => some (.comparison (some .eq))
  | .symbol "!=" => some (.comparison (some .ne))
  | .symbol "<" => some (.comparison (some .lt))
  | .symbol "<=" => some (.comparison (some .le))
  | .symbol ">" => some (.comparison (some .gt))
  | .symbol ">=" => some (.comparison (some .ge))
  | .symbol "+" => some (.arithmetic 5 .add)
  | .symbol "-" => some (.arithmetic 5 .sub)
  | .symbol "*" => some (.arithmetic 6 .mul)
  | .symbol "//" => some (.arithmetic 6 .floorDiv)
  | .symbol "%" => some (.arithmetic 6 .mod)
  | _ => none

-- Binding powers, from weakest to strongest, are conditional, or, and, not,
-- comparison, additive, multiplicative and unary sign. Primaries bind tighter.
-- Every recursive cycle consumes a token. The extra step covers the handoff
-- from an expression's prefix to its infix loop.
mutual

private def parseExpr : Nat → Nat → Stream → Except Diagnostic (SourceExpr × Stream)
  | 0, _, s => failAt .exhausted s
  | fuel + 1, minimum, s => do
    let next := s.pop
    let (left, rest) ← match s.peek.kind with
      | .name name => pure (.read name, next)
      | .integer value => pure (.int (Int.ofNat value), next)
      | .symbol "(" => do
        if next.peek.kind = .symbol ")" then failAt (.unsupported .tuple) s
        else
          let (expr, close) ← parseExpr fuel 0 next
          match close.peek.kind with
          | .symbol ")" => pure (expr, close.pop)
          | .symbol "," => failAt (.unsupported .tuple) close
          | _ => expect "')'" close
      | .symbol "+" => do
        let (arg, rest) ← parseExpr fuel 7 next
        pure (.unary .positive arg, rest)
      | .symbol "-" => do
        let (arg, rest) ← parseExpr fuel 7 next
        pure (.unary .negative arg, rest)
      | .keyword "not" => do
        unless minimum ≤ 3 do return ← expect "an expression" s
        let (arg, rest) ← parseExpr fuel 3 next
        pure (.unary .not arg, rest)
      | .keyword "lambda" =>
        if minimum == 0 then failAt (.unsupported .lambda) s else expect "an expression" s
      | .symbol "[" | .symbol "{" => failAt (.unsupported .collection) s
      | .symbol "~" => failAt (.unsupported .operator) s
      | .plainString _ => failAt (.unsupported .quotedLiteral) s
      | .outside feature => failAt (.unsupported feature) s
      | _ => expect "an expression" s
    parseInfix fuel minimum false left rest

private def parseInfix : Nat → Nat → Bool → SourceExpr → Stream →
    Except Diagnostic (SourceExpr × Stream)
  | 0, _, _, _, s => failAt .exhausted s
  | fuel + 1, minimum, compared, left, s => do
    if let some op := infixOperator s then
      if op.priority < minimum then return (left, s)
      let next := s.pop
      match op with
      | .comparison op =>
        if compared then failAt .chainedComparison s
        else if let some op := op then
          let (right, rest) ← parseExpr fuel 5 next
          parseInfix fuel minimum true (.binary op left right) rest
        else failAt (.unsupported .operator) s
      | .arithmetic p op =>
        let (right, rest) ← parseExpr fuel (p + 1) next
        parseInfix fuel minimum compared (.binary op left right) rest
      | .logical op =>
        let p := (Infix.logical op).priority
        let (right, rest) ← parseExpr fuel (p + 1) next
        parseInfix fuel minimum false (.logical op left right) rest
    else match s.peek.kind with
    | .keyword "if" =>
      if minimum != 0 then return (left, s)
      let (test, afterTest) ← parseExpr fuel 1 s.pop
      unless afterTest.peek.kind = .keyword "else" do return ← expect "'else'" afterTest
      let (no, rest) ← parseExpr fuel 0 afterTest.pop
      return (.conditional test left no, rest)
    | .keyword "not" => expect "'in' after 'not'" s.pop
    | .symbol "(" => failAt (.unsupported .call) s
    | .symbol "[" => failAt (.unsupported .subscript) s
    | .symbol "." => failAt (.unsupported .attribute) s
    | .symbol "/" | .symbol "|" | .symbol "^" | .symbol "&" | .symbol "<<" | .symbol ">>" =>
      failAt (.unsupported .operator) s
    | _ => return (left, s)

end

private def parseSmallStmt (exprFuel : Nat) (inFunction : Bool) (s : Stream) :
    Except Diagnostic (SourceStmt × Stream) := do
  match s.peek.kind with
  | .indent => failAt .unexpectedIndent s
  | .keyword "load" =>
    if inFunction then failAt .loadInFunction s else failAt (.unsupported .loadStatement) s
  | .keyword "break" | .keyword "continue" => failAt (.unsupported .functionControl) s
  | .keyword "return" =>
    unless inFunction do return ← failAt .topLevelReturn s
    let next := s.pop
    match next.peek.kind with
    | .newline | .eof | .symbol ";" => return (.ret none, next)
    | _ =>
      let (value, rest) ← parseExpr exprFuel 0 next
      if rest.peek.kind = .symbol "," then failAt (.unsupported .tuple) rest
      else return (.ret (some value), rest)
  | .keyword "pass" => return (.pass, s.pop)
  | _ =>
    let (left, rest) ← parseExpr exprFuel 0 s
    match rest.peek.kind with
    | .symbol "=" =>
      let .read name := left
        | .error ⟨.invalidAssignmentTarget, ⟨s.peek.span.start, rest.lastEnd⟩⟩
      let (right, rest) ← parseExpr exprFuel 0 rest.pop
      if rest.peek.kind = .symbol "," then failAt (.unsupported .tuple) rest
      else return (.assign name right, rest)
    | .symbol "+=" | .symbol "-=" | .symbol "*=" | .symbol "/=" | .symbol "//=" | .symbol "%="
    | .symbol "&=" | .symbol "|=" | .symbol "^=" | .symbol "<<=" | .symbol ">>=" =>
      failAt (.unsupported .augmentedAssignment) rest
    | .symbol "," => failAt (.unsupported .tuple) rest
    | _ => return (.eval left, rest)

private def consumeSymbol (symbol : String) (s : Stream) : Except Diagnostic Stream :=
  if s.peek.kind = .symbol symbol then .ok s.pop else expect s!"'{symbol}'" s

private def finishSmallStmt (s : Stream) : Except Diagnostic (Bool × Stream) :=
  match s.peek.kind with
  | .eof => .ok (true, s)
  | .newline => .ok (true, s.pop)
  | .symbol ";" => .ok (false, s.pop)
  | _ => expect "a semicolon or end of line" s

private structure SuiteGrammar (Stmt : Type) where
  small : Nat → Bool → Stream → Except Diagnostic (Stmt × Stream)
  branch : SourceExpr → List (LocatedStmt Stmt) → List (LocatedStmt Stmt) → Stmt

private def scalarSuite : SuiteGrammar SourceStmt :=
  ⟨parseSmallStmt, fun test yes no => .branch test (sequence yes) (sequence no)⟩

-- The block loop consumes one statement or newline per iteration. Each descent
-- into a branch suite consumes the heading and its layout tokens.
mutual

private def parseBlock {Stmt : Type} (grammar : SuiteGrammar Stmt) (exprFuel : Nat) (inFunction : Bool) :
    Nat → Bool → Stream → List (LocatedStmt Stmt) → Except Diagnostic (List (LocatedStmt Stmt) × Stream)
  | 0, _, s, _ => failAt .exhausted s
  | fuel + 1, lineStart, s, statements => do
    match s.peek.kind with
    | .eof | .outdent => return (statements.reverse, s)
    | .newline => parseBlock grammar exprFuel inFunction fuel true s.pop statements
    | .keyword "def" | .keyword "for" =>
      if lineStart then failAt (.unsupported .compoundStatement) s
      else expect "a simple statement" s
    | .keyword "if" =>
      unless lineStart do return ← expect "a simple statement" s
      unless inFunction do return ← failAt .topLevelIf s
      let (stmt, rest) ← parseBranch grammar exprFuel fuel s
      let located := ⟨⟨s.peek.span.start, rest.lastEnd⟩, stmt⟩
      parseBlock grammar exprFuel inFunction fuel true rest (located :: statements)
    | _ =>
      let (stmt, rest) ← grammar.small exprFuel inFunction s
      let statements := ⟨⟨s.peek.span.start, rest.lastEnd⟩, stmt⟩ :: statements
      let (lineStart, next) ← finishSmallStmt rest
      parseBlock grammar exprFuel inFunction fuel lineStart next statements

private def parseSuite {Stmt : Type} (grammar : SuiteGrammar Stmt) (exprFuel : Nat) :
    Nat → Stream → Except Diagnostic (List (LocatedStmt Stmt) × Stream)
  | 0, s => failAt .exhausted s
  | fuel + 1, s => do
    match s.peek.kind with
    | .eof => failAt .expectedIndentedSuite s
    | .newline =>
      let next := s.pop
      unless next.peek.kind = .indent do return ← failAt .expectedIndentedSuite next
      let (body, rest) ← parseBlock grammar exprFuel true fuel true next.pop []
      if body.isEmpty then return ← failAt .expectedIndentedSuite rest
      unless rest.peek.kind = .outdent do return ← expect "an outdent" rest
      return (body, rest.pop)
    | _ => failAt (.unsupported .inlineSuite) s

private def parseBranch {Stmt : Type} (grammar : SuiteGrammar Stmt) (exprFuel : Nat) :
    Nat → Stream → Except Diagnostic (Stmt × Stream)
  | 0, s => failAt .exhausted s
  | fuel + 1, s => do
    let (test, afterTest) ← parseExpr exprFuel 0 s.pop
    let (yes, rest) ← parseSuite grammar exprFuel fuel (← consumeSymbol ":" afterTest)
    let (no, rest) ← match rest.peek.kind with
      | .keyword "elif" => do
        let (stmt, afterElif) ← parseBranch grammar exprFuel fuel rest
        pure ([⟨⟨rest.peek.span.start, afterElif.lastEnd⟩, stmt⟩], afterElif)
      | .keyword "else" => parseSuite grammar exprFuel fuel (← consumeSymbol ":" rest.pop)
      | _ => pure ([], rest)
    return (grammar.branch test yes no, rest)

end

private def parserFuel (tokens : List Token) : Nat := 2 * tokens.length + 2

private def parseModuleTokens (tokens : List Token) : Except Diagnostic ParsedModule := do
  let fuel := parserFuel tokens
  let (statements, rest) ← parseBlock scalarSuite fuel false fuel true ⟨tokens, {}⟩ []
  unless rest.peek.kind = .eof do return ← expect "end of file" rest
  return ⟨statements⟩

/-- Parse decoded scalar module text, retaining top-level statement spans. -/
def parseModule (source : String) : Except Diagnostic ParsedModule := do
  parseModuleTokens (← lex source)

/-- Parse original UTF-8 file bytes with the same spans and grammar. -/
def parseModuleUtf8 (source : ByteArray) : Except Diagnostic ParsedModule := do
  parseModuleTokens (← lexUtf8 source)

private def parseName (s : Stream) : Except Diagnostic (String × Stream) :=
  match s.peek.kind with
  | .name name => .ok (name, s.pop)
  | .outside .nonAsciiName => failAt (.unsupported .nonAsciiName) s
  | _ => expect "a name" s

private def parseLocatedExpr (exprFuel : Nat) (s : Stream) :
    Except Diagnostic (LocatedArgument × Stream) := do
  let (expr, rest) ← parseExpr exprFuel 0 s
  return (⟨⟨s.peek.span.start, rest.lastEnd⟩, expr⟩, rest)

private def parseParameters (exprFuel : Nat) (allowDefaults : Bool) :
    Nat → Stream → List LocatedParameter → Except Diagnostic (List LocatedParameter × Stream)
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, parameters => do
    match s.peek.kind with
    | .symbol ")" => return (parameters.reverse, s.pop)
    | .symbol "*" | .symbol "**" => failAt (.unsupported .parameters) s
    | _ =>
      let (name, rest) ← parseName s
      if parameters.any (fun parameter => parameter.name == name) then
        return ← failAt (.duplicateParameter name) s
      let (value, rest) ← if rest.peek.kind = .symbol "=" then do
          unless allowDefaults do return ← failAt (.unsupported .parameters) rest
          let (expr, rest) ← parseLocatedExpr exprFuel rest.pop
          pure (some expr, rest)
        else pure (none, rest)
      let parameters := ⟨⟨s.peek.span.start, rest.lastEnd⟩, name, value⟩ :: parameters
      match rest.peek.kind with
      | .symbol "," => parseParameters exprFuel allowDefaults fuel rest.pop parameters
      | .symbol ")" => return (parameters.reverse, rest.pop)
      | _ => expect "',' or ')'" rest

private def parseFunctionAt {Stmt : Type} (grammar : SuiteGrammar Stmt)
    (fuel : Nat) (allowDefaults : Bool) (s : Stream) :
    Except Diagnostic (LocatedFunction Stmt × Stream) := do
  unless s.peek.kind = .keyword "def" do return ← expect "'def'" s
  let (name, rest) ← parseName s.pop
  let (parameters, rest) ← parseParameters fuel allowDefaults fuel (← consumeSymbol "(" rest) []
  let (body, rest) ← parseSuite grammar fuel fuel (← consumeSymbol ":" rest)
  return (⟨name, parameters, ⟨s.peek.span.start, rest.lastEnd⟩, body⟩, rest)

private def parseFunctionTokens (tokens : List Token) : Except Diagnostic ParsedFunction := do
  let (fn, rest) ← parseFunctionAt scalarSuite (parserFuel tokens) false ⟨tokens, {}⟩
  unless rest.peek.kind = .eof do return ← failAt (.unsupported .functionFile) rest
  return ⟨fn.name, fn.parameters.map LocatedParameter.name, fn.span, fn.body⟩

/-- Parse a file containing one scalar function with an indented body. -/
def parseFunction (source : String) : Except Diagnostic ParsedFunction := do
  parseFunctionTokens (← lex source)

/-- Parse a standalone function from original UTF-8 file bytes. -/
def parseFunctionUtf8 (source : ByteArray) : Except Diagnostic ParsedFunction := do
  parseFunctionTokens (← lexUtf8 source)

private def parseDisplayItems {α : Type} (item : Stream → Except Diagnostic (α × Stream))
    (closing : String) : Nat → Stream → List α → Except Diagnostic (List α × Stream)
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, items => do
    if s.peek.kind = .symbol closing then return (items.reverse, s.pop)
    let (value, rest) ← item s
    let items := value :: items
    if rest.peek.kind = .symbol "," then parseDisplayItems item closing fuel rest.pop items
    else if rest.peek.kind = .symbol closing then return (items.reverse, rest.pop)
    else expect s!"',' or '{closing}'" rest

private def hasExprSuffix (s : Stream) : Bool :=
  (infixOperator s).isSome || match s.peek.kind with
    | .keyword "if" | .symbol "(" | .symbol "[" | .symbol "." | .symbol ","
    | .symbol "/" | .symbol "|" | .symbol "^" | .symbol "&" | .symbol "<<" | .symbol ">>" => true
    | _ => false

private def parseListDisplay (fuel : Nat) (s : Stream) : Except Diagnostic (CollectionDisplay × Stream) := do
  let (elements, rest) ← parseDisplayItems (parseLocatedExpr fuel) "]" fuel s.pop []
  return (.sequence false elements, rest)

-- A single parenthesized operand without a comma belongs to the scalar parser.
private def parseTupleDisplay (fuel : Nat) (s : Stream) :
    Except Diagnostic (Option (CollectionDisplay × Stream)) := do
  let next := s.pop
  if next.peek.kind = .symbol ")" then return some (.sequence true [], next.pop)
  let (first, rest) ← parseLocatedExpr fuel next
  match rest.peek.kind with
  | .symbol "," =>
    let (elements, rest) ← parseDisplayItems (parseLocatedExpr fuel) ")" fuel rest.pop [first]
    return some (.sequence true elements, rest)
  | .symbol ")" => return none
  | _ => expect "',' or ')'" rest

private def parseMappingEntry (fuel : Nat) (s : Stream) :
    Except Diagnostic (LocatedNamedArgument × Stream) := do
  let .plainString key := s.peek.kind | failAt (.unsupported .spreadKey) s
  let (value, rest) ← parseLocatedExpr fuel (← consumeSymbol ":" s.pop)
  return (⟨s.peek.span, key, value⟩, rest)

private def parseMappingDisplay (fuel : Nat) (s : Stream) : Except Diagnostic (CollectionDisplay × Stream) := do
  let (entries, rest) ← parseDisplayItems (parseMappingEntry fuel) "}" fuel s.pop []
  return (.mapping entries, rest)

private def parseCollectionDisplay (fuel : Nat) (s : Stream) :
    Except Diagnostic (Option (CollectionDisplay × Stream)) :=
  match s.peek.kind with
  | .symbol "[" => some <$> parseListDisplay fuel s
  | .symbol "(" => parseTupleDisplay fuel s
  | .symbol "{" => some <$> parseMappingDisplay fuel s
  | _ => pure none

-- Probe only for a head immediately followed by an application. Ordinary
-- parenthesized expressions and tuples still go to their existing parsers.
private def callHead (exprFuel : Nat) (s : Stream) : Option (CallOperand × Stream) := do
  match s.peek.kind with
  | .name name =>
    if s.pop.peek.kind = .symbol "(" then
      some (.scalar ⟨s.peek.span, .read name⟩, s.pop)
    else none
  | .symbol "(" =>
    let (value, close) ← (parseLocatedExpr exprFuel s.pop).toOption
    let rest := close.pop
    if close.peek.kind = .symbol ")" && rest.peek.kind = .symbol "(" then
      some (.scalar ⟨⟨s.peek.span.start, rest.lastEnd⟩, value.expr⟩, rest)
    else none
  | _ => none

-- Every application consumes an opening parenthesis and matching close.
-- Each suffix wraps the expression accumulated so far as its sole callee.
mutual

private def parsePostfixApplications (exprFuel : Nat) :
    Nat → CallOperand → Stream → Except Diagnostic (CallOperand × Stream)
  | 0, _, s => failAt .exhausted s
  | fuel + 1, callee, s => do
    unless s.peek.kind = .symbol "(" do return (callee, s)
    let (arguments, rest) ← parseCallArguments exprFuel fuel s.pop {}
    let application := CallOperand.call ⟨callee.span.start, rest.lastEnd⟩ callee arguments
    parsePostfixApplications exprFuel fuel application rest
termination_by structural fuel _ _ => fuel

private def parseCallOperand (exprFuel : Nat) :
    Nat → Stream → Except Diagnostic (CallOperand × Stream)
  | 0, s => failAt .exhausted s
  | fuel + 1, s => do
    if let some (callee, next) := callHead exprFuel s then
      let (value, rest) ← parsePostfixApplications exprFuel fuel callee next
      if rest.peek.kind != .symbol "," && hasExprSuffix rest then
        return ← failAt (.unsupported .callArguments) rest
      return (value, rest)
    let (value, rest) ← parseLocatedExpr exprFuel s
    return (.scalar value, rest)
termination_by structural fuel _ => fuel

private def parseSpread (exprFuel : Nat) :
    Nat → Bool → Stream → Except Diagnostic (LocatedSpread CallOperand × Stream)
  | 0, _, s => failAt .exhausted s
  | fuel + 1, mapping, s => do
    let next := s.pop
    let parsed ← parseCollectionDisplay exprFuel next
    let (operand, rest) ← match parsed with
      | some (display, rest) =>
        pure (.display ⟨next.peek.span.start, rest.lastEnd⟩ display, rest)
      | none => parseCallOperand exprFuel fuel next
    if let .display _ display := operand then
      match display with
      | .mapping _ => unless mapping do return ← failAt (.unsupported .callArguments) next
      | .sequence .. => if mapping then return ← failAt (.unsupported .callArguments) next
    if rest.peek.kind != .symbol "," && hasExprSuffix rest then
      return ← failAt (.unsupported .callArguments) rest
    return (⟨⟨s.peek.span.start, rest.lastEnd⟩, operand⟩, rest)
termination_by structural fuel _ _ => fuel

-- Preserve explicit names, including repetitions, for the normalized validator.
-- Reject order errors here because the grouped call AST cannot represent them.
private def parseCallItem (exprFuel : Nat) :
    Nat → Stream → LocatedCallArguments → Except Diagnostic (LocatedCallArguments × Stream)
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, args => do
    match s.peek.kind, s.pop.peek.kind with
    | .symbol "**", _ =>
      if args.starStar.isSome then return ← failAt (.callOrder .repeatedStarStar) s
      let (spread, rest) ← parseSpread exprFuel fuel true s
      return ({ args with starStar := some spread }, rest)
    | .symbol "*", _ =>
      if args.starStar.isSome then return ← failAt (.callOrder .argumentAfterStarStar) s
      if args.star.isSome then return ← failAt (.callOrder .repeatedStar) s
      let (spread, rest) ← parseSpread exprFuel fuel false s
      return ({ args with star := some spread }, rest)
    | kind, next =>
      if args.starStar.isSome then return ← failAt (.callOrder .argumentAfterStarStar) s
      if args.star.isSome then return ← failAt (.callOrder .argumentAfterStar) s
      if let (.name name, .symbol "=") := (kind, next) then
        let (value, rest) ← parseCallOperand exprFuel fuel s.pop.pop
        return ({ args with named := ⟨s.peek.span, name, value⟩ :: args.named }, rest)
      if !args.named.isEmpty then return ← failAt (.callOrder .positionalAfterNamed) s
      let (value, rest) ← parseCallOperand exprFuel fuel s
      return ({ args with positional := value :: args.positional }, rest)
termination_by structural fuel _ _ => fuel

private def parseCallArguments (exprFuel : Nat) :
    Nat → Stream → LocatedCallArguments → Except Diagnostic (LocatedCallArguments × Stream)
  | 0, s, _ => failAt .exhausted s
  | fuel + 1, s, args => do
    if s.peek.kind = .symbol ")" then
      return ({ args with positional := args.positional.reverse, named := args.named.reverse }, s.pop)
    let (args, rest) ← parseCallItem exprFuel fuel s args
    match rest.peek.kind with
    | .symbol "," => parseCallArguments exprFuel fuel rest.pop args
    | .symbol ")" =>
      return ({ args with positional := args.positional.reverse, named := args.named.reverse }, rest.pop)
    | _ => expect "',' or ')'" rest
termination_by structural fuel _ _ => fuel

end

private def parseRootCall (exprFuel : Nat) (s : Stream) :
    Except Diagnostic (Option (CallOperand × Stream)) := do
  let some (callee, next) := callHead exprFuel s | return none
  let (value, rest) ← parsePostfixApplications exprFuel (4 * exprFuel) callee next
  if hasExprSuffix rest then failAt (.unsupported .call) rest
  else return some (value, rest)

private def parseFunctionSmall (exprFuel : Nat) (inFunction : Bool) (s : Stream) :
    Except Diagnostic (FunctionStmt × Stream) := do
  if inFunction && s.peek.kind == .keyword "return" then
    if let some (value, rest) ← parseRootCall exprFuel s.pop then
      return (.returnCall value, rest)
  let (stmt, rest) ← parseSmallStmt exprFuel inFunction s
  return (.scalar stmt, rest)

private def moduleSuite : SuiteGrammar FunctionStmt :=
  ⟨parseFunctionSmall, .branch⟩

private def parseFileSmall (exprFuel : Nat) (s : Stream) : Except Diagnostic (FileCommand × Stream) := do
  match s.remaining with
  | ⟨.name target, _⟩ :: ⟨.symbol "=", _⟩ :: _ =>
    let rhs := s.pop.pop
    if let some (value, rest) ← parseRootCall exprFuel rhs then
      return (.assignCall target value, rest)
    if let some (display, rest) ← parseCollectionDisplay exprFuel rhs then
      if hasExprSuffix rest then return ← failAt (.unsupported .collection) rest
      return (.assignDisplay target display, rest)
    let (stmt, rest) ← parseSmallStmt exprFuel false s
    return (.simple stmt, rest)
  | _ =>
    let (stmt, rest) ← parseSmallStmt exprFuel false s
    return (.simple stmt, rest)

private def parseLoadString (description : String) (s : Stream) :
    Except Diagnostic (LocatedString × Stream) :=
  match s.peek.kind with
  | .plainString value => .ok (⟨s.peek.span, value⟩, s.pop)
  | .outside .quotedLiteral => failAt (.unsupported .quotedLiteral) s
  | _ => expect description s

private def parseLoadExport (s : Stream) : Except Diagnostic (LocatedString × Stream) := do
  let (name, rest) ← parseLoadString "a quoted export name" s
  if name.text.toList.any (fun c => c.toNat ≥ 128) then
    return ← failAt (.unsupported .nonAsciiName) s
  unless isAsciiIdentifier name.text do return ← failAt (.invalidImportName name.text) s
  return (name, rest)

private def parseLoadImport (s : Stream) : Except Diagnostic (LocatedImport × Stream) := do
  match s.peek.kind with
  | .name alias =>
    let (name, rest) ← parseLoadExport (← consumeSymbol "=" s.pop)
    return (⟨name, ⟨s.peek.span, alias⟩⟩, rest)
  | .outside .nonAsciiName => failAt (.unsupported .nonAsciiName) s
  | _ =>
    let (name, rest) ← parseLoadExport s
    return (⟨name, name⟩, rest)

private def parseLoad (fuel : Nat) (s : Stream) : Except Diagnostic (FileCommand × Stream) := do
  let (label, rest) ← parseLoadString "a quoted module label" (← consumeSymbol "(" s.pop)
  if rest.peek.kind = .symbol ")" then return ← expect "an imported name" rest
  let next ← consumeSymbol "," rest
  if next.peek.kind = .symbol ")" then return ← expect "an imported name" next
  let (imports, rest) ← parseDisplayItems parseLoadImport ")" fuel next []
  return (.load label imports, rest)

private def parseFileCommands (exprFuel : Nat) :
    Nat → Bool → Bool → Stream → List LocatedFileCommand → Except Diagnostic (List LocatedFileCommand)
  | 0, _, _, s, _ => failAt .exhausted s
  | fuel + 1, lineStart, leading, s, commands => do
    match s.peek.kind with
    | .eof => return commands.reverse
    | .newline => parseFileCommands exprFuel fuel true leading s.pop commands
    | .keyword "def" =>
      unless lineStart do return ← expect "a simple statement" s
      let (fn, rest) ← parseFunctionAt moduleSuite exprFuel true s
      parseFileCommands exprFuel fuel true false rest (⟨fn.span, .define fn⟩ :: commands)
    | .keyword "if" | .keyword "for" =>
      unless lineStart do return ← expect "a simple statement" s
      if s.peek.kind = .keyword "if" then failAt .topLevelIf s
      else failAt (.unsupported .compoundStatement) s
    | _ =>
      let isLoad := s.peek.kind == .keyword "load"
      let (command, rest) ← if isLoad then do
          unless leading do return ← failAt (.unsupported .lateLoad) s
          parseLoad exprFuel s
        else parseFileSmall exprFuel s
      let located := ⟨⟨s.peek.span.start, rest.lastEnd⟩, command⟩
      let (lineStart, next) ← finishSmallStmt rest
      parseFileCommands exprFuel fuel lineStart isLoad next (located :: commands)

private def parseFileTokens (tokens : List Token) : Except Diagnostic (List LocatedFileCommand) :=
  let fuel := parserFuel tokens
  parseFileCommands fuel fuel true true ⟨tokens, {}⟩ []

/-- Parse a file with leading loads, function definitions, and call assignments. -/
def parseFile (source : String) : Except Diagnostic (List LocatedFileCommand) := do
  parseFileTokens (← lex source)

/-- Parse a file with leading loads, function definitions, and call assignments from UTF-8 bytes. -/
def parseFileUtf8 (source : ByteArray) : Except Diagnostic (List LocatedFileCommand) := do
  parseFileTokens (← lexUtf8 source)

end Silmaril.Languages.Starlark.Frontend
