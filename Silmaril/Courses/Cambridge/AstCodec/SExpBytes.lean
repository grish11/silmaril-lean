module

public import Silmaril.Courses.Cambridge.AstCodec
public import Silmaril.Formats.SExp.Dotted.Thms

/-! Cambridge constructor trees as UTF-8 S-expression text. String and
symbol spellings supply the same literal atom to the structural schema.
The canonical output quotes every atom and prints proper lists. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.AstCodec.SExpBytes

open Silmaril.Formats
open Silmaril.Formats.Dasl.Encode (TotalCodec)

def toWire : Tree → DottedSExp.Datum :=
  fold (fun value => .atom (.string value)) SExp2.ofList

mutual

def ofWire? : DottedSExp.Datum → Option Tree
  | .atom value => some (.atom value.value)
  | .nil => some (SExp.ofList [])
  | .cons head tail => do
    return SExp.ofList ((← ofWire? head) :: (← ofList? tail))

/-- Only nil-terminated list spines are part of the structural schema. -/
def ofList? : DottedSExp.Datum → Option (List Tree)
  | .nil => some []
  | .atom _ => none
  | .cons head tail => do return (← ofWire? head) :: (← ofList? tail)

end

private theorem ofList_ofList (values : List DottedSExp.Datum) :
    ofList? (SExp2.ofList values) = values.mapM ofWire? := by
  induction values <;> simp [SExp2.ofList, ofList?, *]

private theorem ofWire_ofList (values : List DottedSExp.Datum) :
    ofWire? (SExp2.ofList values) = (ofList? (SExp2.ofList values)).map SExp.ofList := by
  cases values with
  | nil => rfl
  | cons head tail =>
    simp only [SExp2.ofList, ofWire?, ofList?]
    cases ofWire? head <;> cases ofList? (SExp2.ofList tail) <;> rfl

theorem ofWire_toWire (tree : Tree) : ofWire? (toWire tree) = some tree := by
  induction tree with
  | atom value => rfl
  | list n children ih =>
    change ofWire? (SExp2.ofList (List.ofFn fun i => toWire (children i))) = _
    rw [ofWire_ofList, ofList_ofList, mapM_ofFn_some _ _ _ ih]
    exact congrArg some ((SExp.equivAtomOrList String).symm_apply_apply (.list n children))

/-- Compose a structural codec with the verified dotted S-expression byte format. -/
def codec {α : Type} (shape : Codec α) : TotalCodec α Bytes :=
  (shape.then ⟨toWire, ofWire?, ofWire_toWire⟩).then
    ⟨DottedSExp.encode, DottedSExp.decode, DottedSExp.decode_encode⟩

theorem decode_encode {α : Type} (shape : Codec α) (value : α) :
    (codec shape).decode? ((codec shape).encode value) = some value :=
  (codec shape).recovers value

/-- External data pass the UTF-8 text reader, the proper-list adapter, and
the selected structural schema in order. -/
theorem decode_iff {α : Type} (shape : Codec α) {bytes : Bytes} {value : α} :
    (codec shape).decode? bytes = some value ↔
      ∃ datum tree, DottedSExp.decode bytes = some datum ∧ ofWire? datum = some tree ∧
        shape.decode? tree = some value := by
  simp [codec, TotalCodec.then, Option.bind_eq_some_iff]

theorem encode_injective {α : Type} (shape : Codec α) :
    Function.Injective (codec shape).encode :=
  AstCodec.encode_injective (codec shape)

/-- Canonical input recovers the exact bytes after decoding and re-encoding. -/
theorem reencode_canonical {α : Type} (shape : Codec α) (value : α) :
    ((codec shape).decode? ((codec shape).encode value)).map (codec shape).encode =
      some ((codec shape).encode value) := by
  rw [decode_encode]
  rfl

/-- The emitted bytes have exactly the canonical printed UTF-8 text. -/
theorem text_of_encode {α : Type} (shape : Codec α) (value : α) :
    String.fromUTF8? ((codec shape).encode value).data =
      some (DottedSExp.print (toWire (shape.encode value))) := by
  change String.fromUTF8? (DottedSExp.print (toWire (shape.encode value))).toUTF8 = _
  rw [String.toUTF8_eq_toByteArray, DottedSExp.fromUTF8?_toByteArray]

end Silmaril.Courses.Cambridge.AstCodec.SExpBytes
