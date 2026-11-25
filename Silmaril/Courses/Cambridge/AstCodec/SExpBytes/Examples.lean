module

import Silmaril.Courses.Cambridge.AstCodec.SExpBytes
import Silmaril.Courses.Cambridge.L1.Codec
import Silmaril.Courses.Cambridge.L2.Codec
import Silmaril.Courses.Cambridge.L3.ResolvedCodec
import Silmaril.Courses.Cambridge.ReturnSpecification.Format
meta import Silmaril.Courses.Cambridge.AstCodec.SExpBytes
meta import Silmaril.Courses.Cambridge.L1.Codec
meta import Silmaril.Courses.Cambridge.L2.Codec
meta import Silmaril.Courses.Cambridge.L3.ResolvedCodec
meta import Silmaril.Courses.Cambridge.ReturnSpecification.Format

/-! Regressions for the canonical byte spelling and external S-expression syntax. -/

namespace Silmaril.Courses.Cambridge.AstCodec.SExpBytes.Examples

open Silmaril.Formats

private def utf8 (text : String) : Bytes := ⟨text.toUTF8⟩

private def l1 := codec L1.Codec.termSExp

private def unusualName : String := "λ猫😀 (a;b) | . \" \\ \n\r\t\x00"

private def l1Term : L1.Expr := .assign unusualName (.deref "")

#guard l1.decode? (l1.encode l1Term) = some l1Term
#guard (l1.decode? (l1.encode l1Term)).map l1.encode = some (l1.encode l1Term)
#guard l1.encode (.deref "x()") = utf8 "(\"cambridge-ast-v1\" \"L1\" \"term\" (\"deref\" \"x()\"))"

private def l2 := codec L2.Codec.termSExp
private def l2Term : L2.RawExpr := .lam unusualName .int (.var unusualName)

#guard l2.decode? (l2.encode l2Term) = some l2Term
#guard (codec L2.Codec.typeSExp).decode? (utf8 "(cambridge-ast-v1 L2 type (type-arrow (type-int) (type-unit)))") =
  some (.arr .int .unit)

private def resolved := codec L3.ResolvedCodec.termSExp
private def resolvedTerm : L3.Expr := .lam .int (.assign (.loc 42) (.bvar 0))

#guard match resolved.decode? (resolved.encode resolvedTerm) with
  | some (.lam .int (.assign (.loc 42) (.bvar 0))) => true
  | _ => false

private def external : Bytes :=
  utf8 " ; before\n(cambridge-ast-v1 |L1| term (deref |猫😀 () ; . \\||)) ; after"

#guard l1.decode? external = some (.deref "猫😀 () ; . |")
#guard (l1.decode? external).map l1.encode = some (l1.encode (.deref "猫😀 () ; . |"))
#guard l1.encode (.deref "猫😀 () ; . |") ≠ external

-- The dot is allowed when the resulting list spine is proper.
#guard l1.decode? (utf8 "(cambridge-ast-v1 L1 term . ((deref . (\"λ\"))))") = some (.deref "λ")
#guard l1.decode? (utf8 "(cambridge-ast-v1 L1 term (deref \"\\n\\r\\t\\\\\\\"\"))") =
  some (.deref "\n\r\t\\\"")

private def improper : Bytes := utf8 "(cambridge-ast-v1 L1 term (deref . \"x\"))"

#guard (DottedSExp.decode improper).isSome
#guard (l1.decode? improper).isNone
#guard (l1.decode? (utf8 "(cambridge-ast-v1 L1 term (deref \"\\q\"))")).isNone
#guard (l1.decode? (utf8 "(cambridge-ast-v1 L1 term (skip)) ()")).isNone
#guard (l1.decode? (utf8 "(cambridge-ast-v1 L1 term (deref |unterminated))")).isNone
#guard (l1.decode? (utf8 "(cambridge-ast-v2 L1 term (skip))")).isNone
#guard (l1.decode? (utf8 "(cambridge-ast-v1 L1 type (type-int))")).isNone
#guard (l1.decode? ((l1.encode .skip).push 0xff)).isNone

private abbrev stepContext : StepSpecification.Context := ⟨.l1, 2⟩
private def step := codec (StepSpecification.treeCodec stepContext)

#guard step.decode? (utf8 "(cambridge-step-spec-v1 L1 2 (all (step 0 1)))") = some [(0, (), 1)]

private abbrev returnContext : StepSpecification.Context := ⟨.l3, 3⟩
private def returns := codec (ReturnSpecification.sexp returnContext)
private def claims : ReturnSpecification.Sentence returnContext := [.mayReturn 0, .mayReturnTo 0 2]
private def returnDoc := utf8 "(cambridge-may-return-spec-v1 L3 3 (all (may-return 0) (may-return-to 0 2)))"

#guard returns.decode? returnDoc = some claims
#guard returns.decode? (returns.encode claims) = some claims
#guard (returns.decode? (utf8 "(cambridge-may-return-spec-v1 L3 3 (all (may-return-to 0 3)))")).isNone
#guard (returns.decode? (utf8 "(cambridge-step-spec-v1 L3 3 (all (step 0 2)))")).isNone

end Silmaril.Courses.Cambridge.AstCodec.SExpBytes.Examples
