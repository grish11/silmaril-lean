module

import Silmaril.ProofFormats.TLA.SurfaceSExp.Thms
public meta import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
import all Silmaril.Logic.Temporal.TLA.Surface.Examples
meta import all Silmaril.Logic.Temporal.TLA.Surface.Examples

namespace Silmaril.ProofFormats.TLA.SurfaceSExp.Examples

open Silmaril.Logic.Temporal.TLA.Surface
open Silmaril.Logic.Temporal.TLA.Surface.Examples (boundedQueue dispatcher)

private def recovers {α : Type} (encode : α → Tree) (expected : α)
    (result : Except DecodeError α) : Bool :=
  match result with
  | .ok actual => decide (encode actual = encode expected)
  | .error _ => false

private def rejects {α : Type} (expected : DecodeError) (result : Except DecodeError α) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => decide (actual = expected)

-- The existing queue includes fairness and a hierarchical proof. The dispatcher
-- includes a nested module, a parameterized instance, and an EXCEPT update.
#guard recovers encodeModule boundedQueue
  (decodeModuleBytes (encodeModuleBytes boundedQueue))
#guard recovers encodeModule dispatcher
  (decodeModuleText (encodeModuleText dispatcher))

private def assignment : Expr :=
  .infix (.symbol ":=") (.ref (.operator (.ident "x")) [] []) (.literal (.natural 7))

private def assignmentWire : String :=
  r#"(tla-surface 1 (expr-infix (infix-op-symbol ":=") "# ++
  r#"(expr-ref (ref-head-operator (operator-name-ident (name "x"))) (list) (list)) "# ++
  "(expr-literal (literal-natural 7))))"

#guard encodeExprText assignment == assignmentWire
#guard recovers encodeExpr assignment (decodeExprText assignmentWire)

private def literalWire (literal : String) : String := s!"(tla-surface 1 (expr-literal {literal}))"

-- Alternative transport spellings may denote the same canonical tree.
#guard recovers encodeExpr (.literal (.string "λ|🙂\t\"\\"))
  (decodeExprText r#"  (|tla-surface| |1| (expr-literal (literal-string "λ\|🙂\t\"\\"))) ; tail"#)
#guard recovers encodeExpr (.literal (.decimal 123456789012345678901234567890 "0040"))
  (decodeExprText (literalWire r#"(literal-decimal 123456789012345678901234567890 "0040")"#))
#guard recovers encodeExpr .oldValue (decodeExprText "(tla-surface 1 (expr-old-value . ()))")

#guard rejects .invalidEnvelope (decodeExprText "(tla-surface 2 (expr-old-value))")
#guard rejects .invalidEnvelope (decodeExprText "(tla-surface 01 (expr-old-value))")
#guard rejects .invalidEnvelope (decodeExprText "(tla-surface 1 (expr-old-value) extra)")
#guard rejects .invalidEnvelope (decodeExprText "(tla-surface 1 (expr-old-value) . extra)")
#guard rejects .invalidPayload (decodeModuleText "(tla-surface 1 (expr-old-value))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-unknown))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-old-value extra))")
#guard rejects .invalidPayload (decodeExprText r#"(tla-surface 1 ("expr-old-value"))"#)
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-old-value . extra))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-tuple ()))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-tuple (list . extra)))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-tuple (list (quantifier-exists))))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-cases (list) (some)))")
#guard rejects .invalidPayload (decodeExprText "(tla-surface 1 (expr-cases (list) (none (expr-old-value))))")
#guard rejects .invalidPayload (decodeModuleText r#"(tla-surface 1 (module "M" (list) (list)))"#)
#guard rejects .invalidPayload (decodeModuleText
  r#"(tla-surface 1 (module (name "M") (list) (list (module-unit-directive (directive-use TRUE (citations (list) (list)))))))"#)

#guard rejects .noncanonical (decodeExprText (literalWire "(literal-natural 007)"))
#guard rejects .invalidPayload (decodeExprText (literalWire "(literal-natural -7)"))
#guard rejects .invalidPayload (decodeExprText (literalWire "(literal-natural +7)"))
#guard rejects .invalidPayload (decodeExprText (literalWire "(literal-natural 0x7)"))
#guard rejects .invalidPayload (decodeExprText (literalWire "(literal-natural ７)"))
#guard rejects .invalidPayload (decodeExprText (literalWire r#"(literal-natural "7")"#))
#guard rejects .invalidPayload (decodeExprText (literalWire "(literal-decimal 1 0020)"))
#guard rejects .invalidSExpression (decodeExprText (assignmentWire ++ " ()"))
#guard rejects .invalidSExpression (decodeExprText (assignmentWire ++ " ("))
#guard rejects .invalidSExpression (decodeExprText (literalWire r#"(literal-string "\q")"#))
#guard rejects .invalidSExpression (decodeExprBytes ⟨ByteArray.mk #[0xC0, 0xAF]⟩)

end Silmaril.ProofFormats.TLA.SurfaceSExp.Examples
