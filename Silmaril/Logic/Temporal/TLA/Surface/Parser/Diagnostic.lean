module

public section

namespace Silmaril.Logic.Temporal.TLA.Surface.Parser

/-- A zero-based UTF-8 byte offset and one-based line and column. -/
structure Position where
  byteOffset : Nat
  line : Nat
  column : Nat
  deriving Repr, BEq, Inhabited

/-- A half-open source span. At end of input the span is empty. -/
structure Span where
  start : Position
  stop : Position
  deriving Repr, BEq, Inhabited

inductive DiagnosticKind where
  | lexical
  | syntax
  | precedence
  | unsupported
  deriving Repr, BEq

/-- The first error detected while reading a source. The Surface AST carries no spans. -/
structure Diagnostic where
  kind : DiagnosticKind
  span : Span
  message : String
  deriving Repr

end Silmaril.Logic.Temporal.TLA.Surface.Parser
