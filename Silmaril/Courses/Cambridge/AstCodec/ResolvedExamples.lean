module

import Silmaril.Courses.Cambridge.L2.ResolvedCodec
import Silmaril.Courses.Cambridge.L3.ResolvedCodec
meta import Silmaril.Courses.Cambridge.L2.ResolvedCodec
meta import Silmaril.Courses.Cambridge.L3.ResolvedCodec

/-! Structural regressions for binding indices, record order, and runtime addresses. -/

namespace Silmaril.Courses.Cambridge.AstCodec.ResolvedExamples

def l2Shadowing : L2.Expr :=
  (L2.RawExpr.lam "x" .int
    (.letE "x" .int (.var "x") (.seq (.var "x") (.lam "y" .int (.var "x"))))).resolve []

def expectedShadowing : L2.Expr :=
  .lam .int (.letE .int (.bvar 0) (.seq (.bvar 0) (.lam .int (.bvar 1))))

#guard L2.ResolvedCodec.termSExp.decode? (L2.ResolvedCodec.termSExp.encode l2Shadowing) =
  some expectedShadowing
#guard L2.ResolvedCodec.termJson.decode? (L2.ResolvedCodec.termJson.encode l2Shadowing) =
  some expectedShadowing

def l2Recursive : L2.Expr :=
  (L2.RawExpr.letRecFun "f" "x" .int .int (.app (.var "f") (.var "x")) (.var "f")).resolve []

#guard L2.ResolvedCodec.termSExp.decode? (L2.ResolvedCodec.termSExp.encode l2Recursive) =
  some (.letRecFun .int .int (.app (.bvar 1) (.bvar 0)) (.bvar 0))

#guard L2.ResolvedCodec.termJson.encode (.lam .int (.bvar 0)) ==
  .arr #[.str "cambridge-ast-v1", .str "L2", .str "resolved-term",
    .arr #[.str "lambda", .arr #[.str "type-int"], .arr #[.str "bvar", .str "0"]]]

-- Identical spellings represent a location and a free variable in their own constructors.
def unusualName : String := "λ 猫 \"quoted\"\n\x00"

def l2Locations : L2.Expr := .assign unusualName (.fvar unusualName)

#guard L2.ResolvedCodec.termJson.decode? (L2.ResolvedCodec.termJson.encode l2Locations) =
  some l2Locations
#guard L2.ResolvedCodec.termSExp.decode? (L2.ResolvedCodec.termSExp.encode (.fvar "")) =
  some (.fvar "")

def l3Match : L3.Expr :=
  (L3.RawExpr.lam "x" .int
    (.matchSum (.inl (.var "x") (.sum .int .bool))
      "x" .int (.var "x") "y" .bool (.pair (.var "x") (.var "y")))).resolve []

def seesMatch (decoded : Option L3.Expr) : Bool :=
  match decoded with
  | some (.lam .int (.matchSum (.inl (.bvar 0) (.sum .int .bool))
      .int (.bvar 0) .bool (.pair (.bvar 1) (.bvar 0)))) => true
  | _ => false

#guard seesMatch (L3.ResolvedCodec.termSExp.decode? (L3.ResolvedCodec.termSExp.encode l3Match))
#guard seesMatch (L3.ResolvedCodec.termJson.decode? (L3.ResolvedCodec.termJson.encode l3Match))

def address : Nat := 314159265358979323846

def labels : L3.RecordLabels := ⟨[unusualName, ""], by decide⟩

def l3Runtime : L3.Expr :=
  .record labels fun i =>
    if i.val = 0 then .assign (.loc address) (.ref (.int (-6)))
    else .pair (.deref (.loc address)) (.bvar address)

def seesRuntime (decoded : Option L3.Expr) : Bool :=
  match decoded with
  | some (.record actual fields) =>
    actual.names == [unusualName, ""] &&
      (match List.ofFn fields with
      | [.assign (.loc target) (.ref (.int value)), .pair (.deref (.loc load)) (.bvar index)] =>
        target == address && value == -6 && load == address && index == address
      | _ => false)
  | _ => false

#guard seesRuntime (L3.ResolvedCodec.termSExp.decode? (L3.ResolvedCodec.termSExp.encode l3Runtime))
#guard seesRuntime (L3.ResolvedCodec.termJson.decode? (L3.ResolvedCodec.termJson.encode l3Runtime))

-- The value codec covers even dangling indices. It does not establish well-scoping.
#guard L2.ResolvedCodec.termJson.decode? (L2.ResolvedCodec.termJson.encode (.bvar 8)) = some (.bvar 8)
#guard match L3.ResolvedCodec.termJson.decode? (L3.ResolvedCodec.termJson.encode (.fvar unusualName)) with
  | some (.fvar name) => name == unusualName
  | _ => false

#guard (L2.ResolvedCodec.termJson.decode? (L2.Codec.termJson.encode .skip)).isNone
#guard (L2.Codec.termJson.decode? (L2.ResolvedCodec.termJson.encode .skip)).isNone
#guard (L2.ResolvedCodec.termSExp.decode? (L3.ResolvedCodec.termSExp.encode .skip)).isNone
#guard (L3.ResolvedCodec.termSExp.decode? (L3.Codec.typeSExp.encode .int)).isNone

#guard (L2.ResolvedCodec.termSExp.decode?
  (envelope "L2" "resolved-term" (node "bvar" [.atom "-1"]))).isNone
#guard (L3.ResolvedCodec.termJson.decode? (toJson
  (envelope "L3" "resolved-term" (node "bvar" [.atom "01"])))).isNone
#guard (L2.ResolvedCodec.termSExp.decode?
  (envelope "L2" "resolved-term" (node "loc" [.atom "0"]))).isNone
#guard (L3.ResolvedCodec.termJson.decode? (toJson
  (envelope "L3" "resolved-term" (node "loc" [.atom "-1"])))).isNone
#guard (L3.ResolvedCodec.termSExp.decode?
  (envelope "L3" "resolved-term" (L3.Codec.termTree (.lam "x" .int (.var "x"))))).isNone
#guard (L3.ResolvedCodec.termSExp.decode?
  (envelope "L3" "resolved-term" (node "lambda"
    [.atom "extra-binder", node "type-int" [], node "bvar" [.atom "0"]]))).isNone
#guard (L3.Codec.termJson.decode? (toJson
  (envelope "L3" "term" (L3.ResolvedCodec.termTree (.bvar 0))))).isNone

def duplicateRecord : Tree :=
  let field := node "field" [.atom "", node "loc" [.atom "0"]]
  envelope "L3" "resolved-term" (node "record" [field, field])

#guard (L3.ResolvedCodec.termSExp.decode? duplicateRecord).isNone
#guard (L3.ResolvedCodec.termJson.decode? (toJson duplicateRecord)).isNone
#guard (L3.ResolvedCodec.termSExp.decode?
  (envelope "L3" "resolved-term" (node "store" [node "loc" [.atom "0"]]))).isNone

end Silmaril.Courses.Cambridge.AstCodec.ResolvedExamples
