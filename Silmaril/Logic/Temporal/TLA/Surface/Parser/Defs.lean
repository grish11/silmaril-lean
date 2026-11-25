module

public import Silmaril.Logic.Temporal.TLA.Surface.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Parser.Diagnostic
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Grammar

/-!
# Native TLA+ source parser

See docs/projects/tla-parser.md for grammar coverage and reference validation.
-/

public section

namespace Silmaril.Logic.Temporal.TLA.Surface.Parser

/-- Parse one complete module, including its header and terminator. Whitespace and
comments may surround it. Names, arities and expression levels remain unresolved. -/
def parseModule (source : String) : Except Diagnostic Module :=
  readModule source

/-- Parse one complete expression with the same operator and layout rules as
module bodies. -/
def parseExpr (source : String) : Except Diagnostic Expr :=
  readExpr source

end Silmaril.Logic.Temporal.TLA.Surface.Parser
