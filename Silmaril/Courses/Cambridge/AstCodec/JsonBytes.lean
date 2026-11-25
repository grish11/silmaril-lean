module

public import Silmaril.Courses.Cambridge.AstCodec
public import Silmaril.Formats.JsonWire.Ast.Thms
public import Silmaril.Formats.JsonWire.Encoding.Thms

/-! The Cambridge constructor-tree schema on UTF-8 JSON bytes. The wire
reader accepts RFC 8259 spellings of arrays and Unicode strings. The
encoder chooses the library printer's compact, fully escaped spelling. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.AstCodec.JsonBytes

open Silmaril.Formats
open Silmaril.Formats.Dasl.Encode (TotalCodec)

def toWire : Tree → JsonWire.Ast JsonWire.Decimal :=
  fold (fun text => .scalar (some (.string (JsonWire.stringUnits text))))
    (fun children => .list (RawSyn.ofList children))

mutual

def ofWire? : JsonWire.Ast JsonWire.Decimal → Option Tree
  | .scalar (some (.string units)) => (JsonWire.unitsString? units).map .atom
  | .list children => (ofArray? children).map SExp.ofList
  | _ => none

def ofArray? : JsonWire.Syn JsonWire.Decimal .arr → Option (List Tree)
  | .nil => some []
  | .cons head tail => do return (← ofWire? head) :: (← ofArray? tail)

end

private theorem ofArray_ofList (values : List (JsonWire.Ast JsonWire.Decimal)) :
    ofArray? (RawSyn.ofList values) = values.mapM ofWire? := by
  induction values <;> simp [ofArray?, *]

theorem ofWire_toWire (tree : Tree) : ofWire? (toWire tree) = some tree := by
  induction tree with
  | atom value => simp [toWire, fold, ofWire?, JsonWire.unitsString_stringUnits]
  | list n children ih =>
    change ofWire? (.list (RawSyn.ofList (List.ofFn fun i => toWire (children i)))) = _
    rw [ofWire?, ofArray_ofList, mapM_ofFn_some _ _ _ ih]
    exact congrArg some ((SExp.equivAtomOrList String).symm_apply_apply (.list n children))

/-- Compose a structural AST codec with the verified UTF-8 JSON reader and printer. -/
def codec {α : Type} (shape : Codec α) : TotalCodec α Bytes :=
  (shape.then ⟨toWire, ofWire?, ofWire_toWire⟩).then
    ⟨JsonWire.encode, JsonWire.parse?, JsonWire.parse_encode⟩

theorem decode_encode {α : Type} (shape : Codec α) (value : α) :
    (codec shape).decode? ((codec shape).encode value) = some value :=
  (codec shape).recovers value

/-- Any RFC JSON spelling of the encoded wire tree decodes to the same AST. -/
theorem decode_of_parse {α : Type} (shape : Codec α) (value : α) {bytes : Bytes}
    (parsed : JsonWire.parse? bytes = some (toWire (shape.encode value))) :
    (codec shape).decode? bytes = some value := by
  change (JsonWire.parse? bytes >>= fun wire => ofWire? wire >>= shape.decode?) = some value
  rw [parsed]
  simp [ofWire_toWire, shape.recovers]

theorem encode_injective {α : Type} (shape : Codec α) :
    Function.Injective (codec shape).encode :=
  AstCodec.encode_injective (codec shape)

/-- Decoding and re-encoding canonical input recovers the exact byte string. -/
theorem reencode_canonical {α : Type} (shape : Codec α) (value : α) :
    ((codec shape).decode? ((codec shape).encode value)).map (codec shape).encode =
      some ((codec shape).encode value) := by
  rw [decode_encode]
  rfl

/-- The emitted bytes decode as UTF-8 to the library's exact printed text. -/
theorem text_of_encode {α : Type} (shape : Codec α) (value : α) :
    String.fromUTF8? ((codec shape).encode value).data =
      some (JsonWire.render JsonWire.Decimal.literal (toWire (shape.encode value))) := by
  let text := JsonWire.render JsonWire.Decimal.literal (toWire (shape.encode value))
  change String.fromUTF8? text.toUTF8 = some text
  simp [String.fromUTF8?, String.toUTF8_eq_toByteArray, text.isValidUTF8]

end Silmaril.Courses.Cambridge.AstCodec.JsonBytes
