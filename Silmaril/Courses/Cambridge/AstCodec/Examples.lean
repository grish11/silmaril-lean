module

import Silmaril.Courses.Cambridge.L1.Codec
import Silmaril.Courses.Cambridge.L2.Codec
import Silmaril.Courses.Cambridge.L3.Codec
import Silmaril.Formats.SExp.Printer
meta import Silmaril.Courses.Cambridge.L1.Codec
meta import Silmaril.Courses.Cambridge.L2.Codec
meta import Silmaril.Courses.Cambridge.L3.Codec
meta import Silmaril.Formats.SExp.Printer

/-! Executable schema, arbitrary-name and malformed-input regressions. -/

namespace Silmaril.Courses.Cambridge.AstCodec.Examples

open Silmaril.Formats

def unusualName : String := "λ 猫 ( ) \"quoted\"\\\n\x00"

def l1Term : L1.Expr :=
  .seq (.assign unusualName (.int (-123456789012345678901234567890))) (.deref "")

#guard L1.Codec.termSExp.decode? (L1.Codec.termSExp.encode l1Term) = some l1Term
#guard L1.Codec.termJson.decode? (L1.Codec.termJson.encode l1Term) = some l1Term
#guard L1.Codec.typeSExp.decode? (L1.Codec.typeSExp.encode .bool) = some .bool
#guard L1.Codec.typeJson.decode? (L1.Codec.typeJson.encode .unit) = some .unit

#guard L1.Codec.termJson.encode (.assign "l" (.int (-3))) ==
  .arr #[.str "cambridge-ast-v1", .str "L1", .str "term",
    .arr #[.str "assign", .str "l", .arr #[.str "int", .str "-3"]]]

#guard (do
  let text ← SExpPrinter.printSExp? (L1.Codec.termSExp.encode l1Term)
  let shape ← SExpParser.parseSExp? text
  L1.Codec.termSExp.decode? shape) = some l1Term

#guard (do
  let shape ← (Lean.Json.parse (L1.Codec.termJson.encode l1Term).compress).toOption
  L1.Codec.termJson.decode? shape) = some l1Term

def l2Term : L2.RawExpr :=
  .letRecFun "" unusualName (.arr .int .bool) .bool
    (.app (.var unusualName) (.int 4))
    (.letE "if" .unit .skip (.lam "" .int (.var "")))

#guard L2.Codec.termSExp.decode? (L2.Codec.termSExp.encode l2Term) = some l2Term
#guard L2.Codec.termJson.decode? (L2.Codec.termJson.encode l2Term) = some l2Term
#guard L2.Codec.typeSExp.decode? (L2.Codec.typeSExp.encode (.arr .int .unit)) =
  some (.arr .int .unit)
#guard L2.Codec.typeJson.decode? (L2.Codec.typeJson.encode (.arr .bool .int)) =
  some (.arr .bool .int)

#guard L2.Codec.termJson.encode (.lam "" .unit (.var "let rec")) ==
  .arr #[.str "cambridge-ast-v1", .str "L2", .str "term",
    .arr #[.str "lambda", .str "", .arr #[.str "type-unit"], .arr #[.str "var", .str "let rec"]]]

def labels : L3.RecordLabels := ⟨[unusualName, ""], by decide⟩

def l3Type : L3.Ty :=
  .record labels fun i => if i.val = 0 then .prod .int .bool else .ref (.sum .unit .int)

def l3Term : L3.RawExpr :=
  .record labels fun i =>
    if i.val = 0 then .assign (.loc 314159265358979323846) (.ref (.int (-6)))
    else .project (.var unusualName) ""

def seesType (decoded : Option L3.Ty) : Bool :=
  match decoded with
  | some (.record actual fields) =>
    actual.names == [unusualName, ""] &&
      (match List.ofFn fields with
      | [.prod .int .bool, .ref (.sum .unit .int)] => true
      | _ => false)
  | _ => false

def seesTerm (decoded : Option L3.RawExpr) : Bool :=
  match decoded with
  | some (.record actual fields) =>
    actual.names == [unusualName, ""] &&
      (match List.ofFn fields with
      | [.assign (.loc address) (.ref (.int value)), .project (.var name) label] =>
        address == 314159265358979323846 && value == -6 && name == unusualName && label == ""
      | _ => false)
  | _ => false

#guard seesType (L3.Codec.typeSExp.decode? (L3.Codec.typeSExp.encode l3Type))
#guard seesType (L3.Codec.typeJson.decode? (L3.Codec.typeJson.encode l3Type))
#guard seesTerm (L3.Codec.termSExp.decode? (L3.Codec.termSExp.encode l3Term))
#guard seesTerm (L3.Codec.termJson.decode? (L3.Codec.termJson.encode l3Term))

#guard match L3.Codec.termSExp.decode? (envelope "L3" "term" (node "record" [])) with
  | some (.record fields _) => fields.names.isEmpty
  | _ => false

#guard seesTerm (do
  let shape ← (Lean.Json.parse (L3.Codec.termJson.encode l3Term).compress).toOption
  L3.Codec.termJson.decode? shape)

def matchTerm : L3.RawExpr :=
  .matchSum (.inr (.bool false) (.sum .int .bool))
    "" .int (.var "") unusualName .bool (.var unusualName)

#guard match L3.Codec.termJson.decode? (L3.Codec.termJson.encode matchTerm) with
  | some (.matchSum (.inr (.bool false) (.sum .int .bool)) left .int (.var leftUse)
      right .bool (.var rightUse)) =>
    left == "" && leftUse == "" && right == unusualName && rightUse == unusualName
  | _ => false

#guard (L1.Codec.termSExp.decode? (.atom "skip")).isNone
#guard (L1.Codec.termSExp.decode? (envelope "L1" "term" (node "skip" [.atom "extra"]))).isNone
#guard (L1.Codec.termSExp.decode? (envelope "L1" "term" (node "int" [.atom "-0"]))).isNone
#guard (L1.Codec.termSExp.decode? (envelope "L1" "term" (node "bool" [.atom "False"]))).isNone
#guard (L1.Codec.termSExp.decode? (envelope "L1" "term"
  (node "binary" [node "skip" [], .atom "minus", node "skip" []]))).isNone
#guard (L1.Codec.termJson.decode? (.arr #[.str "cambridge-ast-v1", .str "L1", .str "term",
  .arr #[.str "int", .num 42]])).isNone
#guard (L1.Codec.termJson.decode? (.bool true)).isNone
#guard (L1.Codec.termJson.decode? (Lean.Json.mkObj [("version", .str "cambridge-ast-v1")])).isNone
#guard (L1.Codec.termJson.decode? (toJson (node "cambridge-ast-v2"
  [.atom "L1", .atom "term", node "skip" []]))).isNone
#guard (L1.Codec.termSExp.decode? (L2.Codec.termSExp.encode .skip)).isNone
#guard (L2.Codec.termJson.decode? (L2.Codec.typeJson.encode .int)).isNone
#guard (L2.Codec.termSExp.decode? (envelope "L2" "term"
  (node "lambda" [.atom "x", node "skip" [], node "var" [.atom "x"]]))).isNone

def duplicateTerm : Tree :=
  let field := node "field" [.atom unusualName, node "skip" []]
  envelope "L3" "term" (node "record" [field, field])

def duplicateType : Tree :=
  let field := node "type-field" [.atom "", node "type-int" []]
  envelope "L3" "type" (node "type-record" [field, field])

#guard (L3.Codec.termSExp.decode? duplicateTerm).isNone
#guard (L3.Codec.termJson.decode? (toJson duplicateTerm)).isNone
#guard (L3.Codec.typeSExp.decode? duplicateType).isNone
#guard (L3.Codec.typeJson.decode? (toJson duplicateType)).isNone
#guard (L3.Codec.termSExp.decode? (envelope "L3" "term" (node "loc" [.atom "-1"]))).isNone
#guard (L3.Codec.termJson.decode? (toJson (envelope "L3" "term" (node "loc" [.atom "01"])))).isNone
#guard (L3.Codec.termSExp.decode? (envelope "L3" "term"
  (node "record" [node "type-field" [.atom "x", node "type-int" []]]))).isNone
#guard (L3.Codec.typeSExp.decode? (envelope "L3" "type"
  (node "type-record" [node "type-field" [.atom "x"]]))).isNone

end Silmaril.Courses.Cambridge.AstCodec.Examples
