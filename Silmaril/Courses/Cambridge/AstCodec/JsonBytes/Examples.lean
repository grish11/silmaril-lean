module

import Silmaril.Courses.Cambridge.AstCodec.JsonBytes
import Silmaril.Courses.Cambridge.L1.Codec
import Silmaril.Courses.Cambridge.L3.ResolvedCodec
meta import Silmaril.Courses.Cambridge.AstCodec.JsonBytes
meta import Silmaril.Courses.Cambridge.L1.Codec
meta import Silmaril.Courses.Cambridge.L3.ResolvedCodec

/-! Regressions for canonical JSON bytes, external RFC syntax, and invalid input. -/

namespace Silmaril.Courses.Cambridge.AstCodec.JsonBytes.Examples

open Silmaril.Formats

def utf8 (text : String) : Bytes := ⟨text.toUTF8⟩

def l1 := codec L1.Codec.termSExp

def l1Assignment : L1.Expr := .assign "猫😀" (.int (-9007199254740993))

#guard l1.decode? (l1.encode l1Assignment) = some l1Assignment
#guard (l1.decode? (l1.encode l1Assignment)).map l1.encode = some (l1.encode l1Assignment)

def l1WithControls : L1.Expr := .deref "λ\x00\n\"\\😀"

#guard l1.decode? (l1.encode l1WithControls) = some l1WithControls
#guard JsonWire.encode (toWire (.atom "a😀")) = utf8 "\"\\u0061\\ud83d\\ude00\""

-- The existing JSON value schema also describes the emitted text.
#guard (do
  let printed ← String.fromUTF8? (l1.encode l1Assignment).data
  (Lean.Json.parse printed).toOption) == some (L1.Codec.termJson.encode l1Assignment)

def external : Bytes :=
  utf8 " [ \"cambridge-ast-v1\", \"L1\", \"term\",\n\t[\"assign\", \"猫😀\", [\"int\", \"-9007199254740993\"]] ] "

def externalEscaped : Bytes :=
  utf8 "[\"cambridge-ast-v1\",\"L1\",\"term\",[\"assign\",\"猫\\ud83d\\ude00\",[\"int\",\"-9007199254740993\"]]]"

#guard l1.decode? external = some l1Assignment
#guard l1.decode? externalEscaped = some l1Assignment
#guard (l1.decode? external).map l1.encode = some (l1.encode l1Assignment)
#guard l1.encode l1Assignment ≠ external

-- A syntactically valid RFC surrogate escape can still violate the scalar-string schema.
def loneSurrogate : Bytes :=
  utf8 "[\"cambridge-ast-v1\",\"L1\",\"term\",[\"deref\",\"\\ud800\"]]"

#guard (JsonWire.parse? loneSurrogate).isSome
#guard (l1.decode? loneSurrogate).isNone
#guard (l1.decode? ⟨ByteArray.mk #[0x22, 0xc0, 0xaf, 0x22]⟩).isNone
#guard (l1.decode? (utf8 "[\"cambridge-ast-v1\",\"L1\",\"term\",[\"int\",42]]")).isNone
#guard (l1.decode? (utf8 "[\"cambridge-ast-v1\",\"L1\",\"term\",[\"int\",\"01\"]]")).isNone
#guard (l1.decode? (utf8 "[\"cambridge-ast-v1\",\"L1\",\"term\",{\"skip\":true}]")).isNone
#guard (l1.decode? (utf8 "[\"cambridge-ast-v1\",\"L1\",\"type\",[\"type-int\"]]")).isNone
#guard (l1.decode? (utf8 "[\"cambridge-ast-v1\",\"L1\",\"term\",[\"skip\",]]")).isNone
#guard (l1.decode? (external.append (utf8 " []"))).isNone
#guard (l1.decode? ((utf8 "/*comment*/").append external)).isNone

def l3 := codec L3.ResolvedCodec.termSExp

def l3Assignment : L3.Expr :=
  .lam (.ref .int) (.assign (.bvar 0) (.deref (.loc 42)))

def seesL3Assignment : Option L3.Expr → Bool
  | some (.lam (.ref .int) (.assign (.bvar 0) (.deref (.loc 42)))) => true
  | _ => false

#guard seesL3Assignment (l3.decode? (l3.encode l3Assignment))
#guard seesL3Assignment (l3.decode? (utf8
  ("[\"cambridge-ast-v1\",\"L3\",\"resolved-term\",[\"lambda\",[\"type-ref\",[\"type-int\"]]," ++
    "[\"assign\",[\"bvar\",\"0\"],[\"deref\",[\"loc\",\"42\"]]]]]")))

-- The two source spellings of the record label denote the same name.
def duplicateLabels : Bytes := utf8
  ("[\"cambridge-ast-v1\",\"L3\",\"resolved-term\",[\"record\"," ++
    "[\"field\",\"p\",[\"loc\",\"0\"]],[\"field\",\"\\u0070\",[\"loc\",\"1\"]]]]")

#guard (JsonWire.parse? duplicateLabels).isSome
#guard (l3.decode? duplicateLabels).isNone
#guard (l3.decode? ((codec L3.Codec.termSExp).encode .skip)).isNone

end Silmaril.Courses.Cambridge.AstCodec.JsonBytes.Examples
