module

public import Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Lexer.Defs
import all Silmaril.Languages.Starlark.Denotation.Defs
import all Silmaril.Languages.Starlark.Resolve.Defs
meta import Silmaril.Languages.Starlark.Defs

namespace Silmaril.Languages.Starlark.Frontend

public structure Fixture where
  name : String
  source : String
  diagnostic : Option DiagnosticKind
  goAccepts : Bool
  isFunction : Bool

private def accept (name source : String) : Fixture := ⟨name, source, none, true, false⟩

private def reject (name source : String) (kind : DiagnosticKind) : Fixture :=
  ⟨name, source, some kind, false, false⟩

private def outside (name source : String) (feature : Feature) : Fixture :=
  ⟨name, source, some (.unsupported feature), true, false⟩

private def multiline := "# λ🙂\r\nout = (2 +\r\n  3)  # 文\r\nnext = out"

private def denotationSource :=
  "# coût 😀\nbase = 0x10 + 0o3 * 2\nout = -base // 5 + 4 if not False and 2 < 3 else 1 // 0"

private def functionCase (name source : String) (diagnostic : Option DiagnosticKind := none)
    (goAccepts : Bool := true) : Fixture :=
  ⟨name, source, diagnostic, goAccepts, true⟩

private def nestedSuite :=
  "# choix\r\ndef pick(\r\n  flag,\r\n):\r\n  if flag:\r\n\t# 雪\r\n \t\r\n" ++
  "    if (1 +\r\n\t2) == 3:\r\n      return \\\r\n\t8\r\n    else:\r\n      return 0\r\n" ++
  "  else:\r\n    return -1"

private def eofSuite := "def f():\r\n  if 1:\r\n    return 2"

private def lineDedent := "def f():\n  if 1:\n    return 2\n\n# dedent at the next code\n  return 3"

private def badDedent := "def f():\n  if 1:\n    return 2\n   return 3"

/-- Both parsers receive the same source spelling. Go's result is syntax-only. -/
public def fixtures : List Fixture := [
  accept "empty" "",
  accept "comment-only" "  # 雪\n \t\n",
  accept "multiline-crlf" multiline,
  accept "bare-cr" "x = 1\ry = x",
  accept "denotation" denotationSource,
  accept "simple-statements" "pass; (x) = 0; x;\n",
  accept "associativity" "x = (+20 - 8 - 3) % 4 or 0 and None",
  accept "parenthesized-comparison" "x = (1 < 2) == True",
  accept "upper-radix-and-big-int" "out = 0XFF + 0O7 + 123456789012345678901234567890",
  accept "duplicate-global-syntax" "x = 1\nx = 2\n",
  reject "missing-rhs" "x = # nothing follows\n" (.expected "an expression"),
  reject "missing-group-closer" "x = (1 + 2" (.unclosedDelimiter ")"),
  reject "missing-else" "x = 1 if True" (.expected "'else'"),
  reject "chained-comparison" "x = 1 <= 2 < 3" .chainedComparison,
  reject "chained-membership" "x = 1 == 2 not in values" .chainedComparison,
  reject "not-incomplete" "x = 1 not 2" (.expected "'in' after 'not'"),
  reject "not-after-add" "x = 1 + not False" (.expected "an expression"),
  reject "missing-statement-separator" "x = 1 y = 2" (.expected "a semicolon or end of line"),
  reject "invalid-character" "x = !1" (.invalidCharacter '!'),
  reject "leading-zero" "x = 0755" .invalidInteger,
  reject "invalid-radix" "x = 0o8" .invalidInteger,
  reject "invalid-exponent" "x = 1e-" .invalidFloat,
  reject "unclosed-quote" "x = 'hello\n" .unterminatedQuote,
  reject "unexpected-indent" "  x = 1\n" .unexpectedIndent,
  outside "unicode-name" "λ = 1\nout = λ" .nonAsciiName,
  outside "suite" "def f():\n    return 1\n" .compoundStatement,
  outside "load" "load('a.star', 'name')" .loadStatement,
  outside "tuple-rhs" "x = 1, 2" .tuple,
  outside "collection" "x = [1]" .collection,
  outside "call" "x = f(2)" .call,
  outside "subscript" "x = a[2]" .subscript,
  outside "attribute" "x = a.field" .attribute,
  outside "shift" "x = 1 << 2" .operator,
  outside "membership" "x = 1 not in a" .operator,
  outside "float" "x = .25e+2" .floatLiteral,
  outside "quoted" "x = rb'''雪\n# still part of the literal'''" .quotedLiteral,
  accept "explicit-join-lf" "x = 1 + \\\n  2",
  accept "explicit-join-crlf" "x = 1 + \\\r\n\t2\r\n",
  accept "explicit-join-cr" "x = 1 + \\\r  2",
  accept "inline-tabs" "x\t=\t1 +\t2",
  reject "backslash-before-space" "x = 1 + \\ \n  2" (.invalidCharacter '\\'),
  reject "form-feed" "x = \x0c1" (.invalidCharacter '\x0c'),
  reject "unexpected-closer" "x = 1)" (.unexpectedCloser ")"),
  reject "mismatched-closer" "x = (\n  1]" (.mismatchedCloser ")" "]"),
  outside "list-continuation" "x = [\r\n  # snow\r\n\t1,\r\n]\r\n" .collection,
  outside "dict-continuation" "x = {\n\n  1: 2,\n}\n" .collection,
  ⟨"unassignable-target", "1 = 2", some .invalidAssignmentTarget, true, false⟩,
  ⟨"go-binary-literal", "x = 0b10", some .invalidInteger, true, false⟩,
  ⟨"go-assert-name", "assert = 2", some (.reservedWord "assert"), true, false⟩,
  ⟨"top-level-if", "if True:\n  pass", some .topLevelIf, true, false⟩,
  ⟨"top-level-return", "return 1", some .topLevelReturn, true, false⟩,
  functionCase "nested-suites" nestedSuite,
  functionCase "two-outdents-at-eof" eofSuite,
  functionCase "bare-cr-suite" "def f():\r  return 2\r",
  functionCase "outdent-at-peer-line" lineDedent,
  functionCase "elif-and-bare-return" "def f(x):\n  if x:\n    return\n  elif 1:\n    return x\n",
  functionCase "trailing-semicolon" "def f():\n  pass; return 1;",
  functionCase "comments-at-eof" "def f():\n  return 2\n  # done\n \t",
  functionCase "mismatched-dedent" badDedent (some (.mismatchedDedent 3)) false,
  functionCase "missing-suite" "def f():\n    # only a comment" (some .expectedIndentedSuite) false,
  functionCase "join-without-suite" "def f():\n  \\\n" (some .expectedIndentedSuite) false,
  functionCase "unexpected-indent-in-suite" "def f():\n  pass\n    return 1"
    (some .unexpectedIndent) false,
  functionCase "compound-after-semicolon" "def f():\n  pass; if True:\n    return 1"
    (some (.expected "a simple statement")) false,
  functionCase "tab-matches-eight-spaces-in-go" "def f():\r\n\tpass\r\n        return 1"
    (some .tabIndent),
  functionCase "space-then-tab-in-go" "def f():\n \tpass\n        return 1" (some .tabIndent),
  functionCase "two-tabs-match-fifteen-spaces-in-go" "def f():\n\t\tpass\n               return 1"
    (some .tabIndent),
  functionCase "two-tabs-miss-sixteen-spaces-in-go" "def f():\n                pass\n\t\treturn 1"
    (some .tabIndent) false,
  functionCase "inline-suite" "def f(): return 1" (some (.unsupported .inlineSuite)),
  functionCase "default-parameter" "def f(x=1):\n  return x" (some (.unsupported .parameters)),
  functionCase "duplicate-parameter" "def f(x, x):\n  return x" (some (.duplicateParameter "x")),
  functionCase "statement-after-function" "def f():\n  return 1\nx = 2"
    (some (.unsupported .functionFile))]

private def Fixture.check (fixture : Fixture) : Bool :=
  let bytes := fixture.source.toUTF8
  let result := if fixture.isFunction then (parseFunctionUtf8 bytes).map (fun _ => ())
    else (parseModuleUtf8 bytes).map (fun _ => ())
  match result with
  | .ok _ => fixture.diagnostic.isNone
  | .error error => decide (fixture.diagnostic = some error.kind)

#guard fixtures.all Fixture.check

-- No prefix of a successful layout may close an unopened level. At EOF all
-- levels must be closed and the EOF must be the final token.
private def balancedLayout : Nat → List Token → Bool
  | depth, ⟨.indent, _⟩ :: rest => balancedLayout (depth + 1) rest
  | 0, ⟨.outdent, _⟩ :: _ => false
  | depth + 1, ⟨.outdent, _⟩ :: rest => balancedLayout depth rest
  | depth, ⟨.eof, _⟩ :: rest => depth == 0 && rest.isEmpty
  | depth, _ :: rest => balancedLayout depth rest
  | _, [] => false

private def Fixture.checkLayout (fixture : Fixture) : Bool :=
  match lexUtf8 fixture.source.toUTF8 with
  | .ok tokens => balancedLayout 0 tokens
  | .error _ => true

#guard fixtures.all Fixture.checkLayout

private def denotedGlobal (source name : String) : Option Value :=
  (do
    let parsed ← (parseModuleUtf8 source.toUTF8).toOption
    let globals ← (runModule parsed.toSourceStmt).toOption
    globals name)

-- UTF-8 file bytes → scalar AST → unchanged resolver and denotation.
#guard decide (denotedGlobal denotationSource "out" = some (.int (-1)))

example : denotedGlobal "out = 2 + 3" "out" = some (.int 5) := by decide +kernel

#guard decide (denotedGlobal "x = 20 - 8 - 3" "x" = some (.int 9) ∧
    denotedGlobal "y = 1 or 0 and 0" "y" = some (.int 1) ∧
    denotedGlobal "z = 1 if True else 2 if False else 3" "z" = some (.int 1) ∧
    denotedGlobal "z = not 2 < 3" "z" = some (.bool false))

private def endToEndFailure (source : String) : Option Failure :=
  match parseModule source with
  | .ok parsed =>
    match runModule parsed.toSourceStmt with
    | .error failure => some failure
    | .ok _ => none
  | .error _ => none

#guard decide (endToEndFailure "x = 1\nx = 2" = some (.static (.duplicateGlobal "x")) ∧
    endToEndFailure "x = 1 // 0" = some (.dynamic (.zeroDivisor .floorDiv)))

private def statementSpans : Option (List Span) := do
  let parsed ← (parseModuleUtf8 multiline.toUTF8).toOption
  return parsed.statements.map LocatedStmt.span

example : statementSpans = some [⟨⟨10, 2, 1⟩, ⟨26, 3, 5⟩⟩, ⟨⟨35, 4, 1⟩, ⟨45, 4, 11⟩⟩] :=
  by decide +kernel

private def newlineSpans : Option (List Span) := do
  let tokens ← (lex multiline).toOption
  return (tokens.filter (fun t => decide (t.kind = .newline))).map Token.span

example : newlineSpans = some [⟨⟨33, 3, 10⟩, ⟨35, 4, 1⟩⟩] :=
  by decide +kernel

private def diagnostic (source : ByteArray) : Option Diagnostic :=
  match parseModuleUtf8 source with
  | .ok _ => none
  | .error error => some error

example : diagnostic ("# 文\r\nx =".toUTF8) =
    some ⟨.expected "an expression", ⟨⟨10, 2, 4⟩, ⟨10, 2, 4⟩⟩⟩ := by decide +kernel

example : diagnostic ("x = café".toUTF8) =
    some ⟨.unsupported .nonAsciiName, ⟨⟨4, 1, 5⟩, ⟨9, 1, 9⟩⟩⟩ := by decide +kernel

example : diagnostic ("# λ\r\n# 😀".toUTF8.push 0xC0) =
    some ⟨.invalidUtf8, ⟨⟨12, 2, 4⟩, ⟨13, 2, 5⟩⟩⟩ := by decide +kernel

private def denotedFunction (source : String) (parameters : List (String × Value)) : Option Value := do
  let parsed ← (parseFunctionUtf8 source.toUTF8).toOption
  (runFunctionBody [] parameters parsed.toSourceStmt).toOption

-- Actual multiline function text, with both open levels closed at EOF.
example : denotedFunction eofSuite [] = some (.int 2) := by decide +kernel

#guard decide (denotedFunction nestedSuite [("flag", .bool true)] = some (.int 8) ∧
    denotedFunction nestedSuite [("flag", .bool false)] = some (.int (-1)) ∧
    denotedFunction "def f():\n  if 0:\n    return 1\n  elif 1:\n    return\n  else:\n    return 2"
      [] = some Value.none)

private def functionHeader : Option (String × List String) := do
  let parsed ← (parseFunction "def pick(a,\n  b,):\n  return b").toOption
  return (parsed.name, parsed.parameters)

example : functionHeader = some ("pick", ["a", "b"]) := by decide +kernel

private def functionSpans : Option (Span × List Span) := do
  let parsed ← (parseFunction lineDedent).toOption
  return (parsed.span, parsed.body.map LocatedStmt.span)

example : functionSpans = some (⟨⟨0, 1, 1⟩, ⟨67, 6, 11⟩⟩,
    [⟨⟨11, 2, 3⟩, ⟨29, 3, 13⟩⟩, ⟨⟨59, 6, 3⟩, ⟨67, 6, 11⟩⟩]) := by decide +kernel

private def layoutSpans (source : String) (kind : TokenKind) : Option (List Span) := do
  let tokens ← (lexUtf8 source.toUTF8).toOption
  return (tokens.filter (fun token => decide (token.kind = kind))).map Token.span

example : layoutSpans eofSuite .indent = some [⟨⟨10, 2, 1⟩, ⟨12, 2, 3⟩⟩, ⟨⟨19, 3, 1⟩, ⟨23, 3, 5⟩⟩] ∧
    layoutSpans eofSuite .newline = some [⟨⟨8, 1, 9⟩, ⟨10, 2, 1⟩⟩,
      ⟨⟨17, 2, 8⟩, ⟨19, 3, 1⟩⟩, ⟨⟨31, 3, 13⟩, ⟨31, 3, 13⟩⟩] ∧
    layoutSpans eofSuite .outdent = some [⟨⟨31, 3, 13⟩, ⟨31, 3, 13⟩⟩, ⟨⟨31, 3, 13⟩, ⟨31, 3, 13⟩⟩] :=
  by decide +kernel

example : layoutSpans lineDedent .outdent =
    some [⟨⟨59, 6, 3⟩, ⟨59, 6, 3⟩⟩, ⟨⟨67, 6, 11⟩, ⟨67, 6, 11⟩⟩] := by decide +kernel

example : diagnostic badDedent.toUTF8 =
    some ⟨.mismatchedDedent 3, ⟨⟨30, 4, 1⟩, ⟨33, 4, 4⟩⟩⟩ := by decide +kernel

example : diagnostic "x = (\r\n  1]".toUTF8 =
    some ⟨.mismatchedCloser ")" "]", ⟨⟨10, 2, 4⟩, ⟨11, 2, 5⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend
