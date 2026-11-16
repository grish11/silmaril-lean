module

public import Silmaril.Wasm.Component.Reference.WIT.Repr.Defs
public import Silmaril.Formats.JsonEvents.Defs
public import Silmaril.Formats.JsonWire.Ast.Defs
public import Silmaril.Formats.JsonBytes.Defs
public import Silmaril.Formats.JsonLines.Defs

/-! # JSON event streams and JSON Lines as WIT values: definitions

WIT types are not recursive, so a JSON tree has no WIT type. Its event stream
(`Silmaril.Formats.JsonEvents`) does:

```wit
variant json-event {
  scalar(S), begin-array, end-array, begin-object, key(K), end-object,
}
```

and a stream is `list<json-event>`.

* `eventType tk ts`, `Repr.event rk rs`, `Repr.events rk rs`: the WIT `variant` above for any
  WIT representations `rk` of the keys and `rs` of the scalars, and `list<…>` of it (through the
  existing `Repr.stream`). The semantic event type is `JsonEvents.Event K S`, not a copy.
* **Payloads explicitly representable in WIT** (`Repr.units`, `Repr.wireScalar`):
  * keys and string scalars as UTF-16 code units, `list<u16>` (`JsonWire.Units`). This keeps
    lone surrogates, which JSON escapes can produce and a WIT `string` (Unicode scalar values)
    cannot carry;
  * scalars as the `JsonWire.Scalar N` of the wire AST: `none` is `null`, then `bool`,
    `string` and `number` atoms, as `variant json-scalar { null, %bool(bool),
    %string(list<u16>), number(N) }`;
  * numbers as their **lexeme**, `list<u8>` (`N := List UInt8`). `Repr.wireEvents` is the
    resulting stream interface.
* **Validity is in the specification, not the type.** The types admit every list of events and
  every byte list as a number:
  * `eventLang okK okS`: the well-formed streams (`JsonEvents.language`, those encoding a tree)
    whose keys satisfy `okK` and scalars `okS`;
  * `eventLangAt okK okS d`: the same with nesting depth at most `d`
    (`Silmaril.Streams.DepthBound Event.kind d`, the depth of `JsonEvents`);
  * `NumberLexeme`: a number payload is lexically valid when it matches RFC 8259 §6
    (`JsonBytes.number`). `wireOk` is that constraint on wire scalars, with string contents
    unconstrained (every UTF-16 sequence is reachable through escapes).
* **JSON Lines as items** (`linesLang pol L`): the lists of lines each allowed by a
  `JsonLines.Policy` over a line-content language `L`, carried as `list<list<u8>>` by the
  existing `Repr.items`. `Thms` relates them to the byte language `JsonLines.frameLang`.

No lexer from bytes to events is defined or proved here: these events are not related to the
byte languages `JsonBytes.language`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource}

/-- **The WIT `json-event` variant** with key type `tk` and scalar type `ts`. -/
def eventType (tk ts : ValType Ref Resource) : ValType Ref Resource :=
  .variant [("scalar", some ts), ("begin-array", none), ("end-array", none),
    ("begin-object", none), ("key", some tk), ("end-object", none)]

/-- `list<u16>`: UTF-16 code units. -/
def unitsType : ValType Ref Resource := .list (.prim .u16)

/-- **The WIT `json-scalar` variant** with number type `tn`. -/
def wireScalarType (tn : ValType Ref Resource) : ValType Ref Resource :=
  .variant [("null", none), ("bool", some (.prim .bool)), ("string", some unitsType),
    ("number", some tn)]

namespace Repr

variable {K S N : Type}

/-- The events as a right-nested sum, in the order of the variant's cases. -/
def eventEquiv : JsonEvents.Event K S ≃ S ⊕ Unit ⊕ Unit ⊕ Unit ⊕ K ⊕ Unit ⊕ Empty where
  toFun
    | .scalar s => .inl s
    | .beginArray => .inr (.inl ())
    | .endArray => .inr (.inr (.inl ()))
    | .beginObject => .inr (.inr (.inr (.inl ())))
    | .key k => .inr (.inr (.inr (.inr (.inl k))))
    | .endObject => .inr (.inr (.inr (.inr (.inr (.inl ())))))
  invFun
    | .inl s => .scalar s
    | .inr (.inl ()) => .beginArray
    | .inr (.inr (.inl ())) => .endArray
    | .inr (.inr (.inr (.inl ()))) => .beginObject
    | .inr (.inr (.inr (.inr (.inl k)))) => .key k
    | .inr (.inr (.inr (.inr (.inr (.inl ()))))) => .endObject
  left_inv e := by cases e <;> rfl
  right_inv x := by
    rcases x with s | ⟨⟩ | ⟨⟩ | ⟨⟩ | k | ⟨⟩ | x
    all_goals first | rfl | exact x.elim

/-- **One event** as a `json-event`. -/
def event {tk ts : ValType Ref Resource} (rk : Repr E K tk) (rs : Repr E S ts) :
    Repr E (JsonEvents.Event K S) (eventType tk ts) :=
  eventEquiv.trans (Equiv.sumCongr rs (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr
    (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr rk (Equiv.refl _))))))

/-- **An event stream** as `list<json-event>`. -/
def events {tk ts : ValType Ref Resource} (rk : Repr E K tk) (rs : Repr E S ts) :
    Repr E (List (JsonEvents.Event K S)) (.list (eventType tk ts)) :=
  stream (event rk rs)

/-- UTF-16 code units as `list<u16>`. -/
def units : Repr E JsonWire.Units unitsType := list (prim .u16)

/-- Wire scalars as a right-nested sum. -/
def wireScalarEquiv : JsonWire.Scalar N ≃ Unit ⊕ Bool ⊕ JsonWire.Units ⊕ N ⊕ Empty where
  toFun
    | none => .inl ()
    | some (.bool b) => .inr (.inl b)
    | some (.string s) => .inr (.inr (.inl s))
    | some (.number n) => .inr (.inr (.inr (.inl n)))
  invFun
    | .inl () => none
    | .inr (.inl b) => some (.bool b)
    | .inr (.inr (.inl s)) => some (.string s)
    | .inr (.inr (.inr (.inl n))) => some (.number n)
  left_inv x := by rcases x with _ | (_ | _ | _) <;> rfl
  right_inv x := by
    rcases x with ⟨⟩ | b | s | n | x
    all_goals first | rfl | exact x.elim

/-- **Wire scalars** as `json-scalar`, from a representation of numbers. -/
def wireScalar {tn : ValType Ref Resource} (rn : Repr E N tn) :
    Repr E (JsonWire.Scalar N) (wireScalarType tn) :=
  wireScalarEquiv.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _)
    (Equiv.sumCongr units (Equiv.sumCongr rn (Equiv.refl _)))))

/-- **The JSON event-stream interface**: keys `list<u16>`, numbers as lexemes `list<u8>`. -/
def wireEvents :
    Repr E (List (JsonEvents.Event JsonWire.Units (JsonWire.Scalar (List UInt8))))
      (.list (eventType unitsType (wireScalarType .bytes))) :=
  events units (wireScalar bytes)

end Repr

namespace Json

variable {K S : Type}

/-- An event whose key satisfies `okK` or whose scalar satisfies `okS` (brackets always). -/
def ValidEvent (okK : K → Prop) (okS : S → Prop) : JsonEvents.Event K S → Prop
  | .scalar s => okS s
  | .key k => okK k
  | _ => True

/-- **Valid event streams**: well-formed, with valid keys and scalars. -/
def eventLang (okK : K → Prop) (okS : S → Prop) : Language (JsonEvents.Event K S) :=
  {es | es ∈ JsonEvents.language K S ∧ ∀ e ∈ es, ValidEvent okK okS e}

/-- Valid event streams of nesting depth at most `d`. -/
def eventLangAt (okK : K → Prop) (okS : S → Prop) (d : Nat) : Language (JsonEvents.Event K S) :=
  eventLang okK okS ⊓ Silmaril.Streams.DepthBound JsonEvents.Event.kind d

/-- A number payload is an RFC 8259 §6 number lexeme. -/
def NumberLexeme (n : List UInt8) : Prop := n ∈ JsonBytes.number.matches'

/-- Wire scalars with lexically valid numbers (string contents unconstrained). -/
def wireOk : JsonWire.Scalar (List UInt8) → Prop
  | some (.number n) => NumberLexeme n
  | _ => True

/-- **JSON Lines as items**: lists of lines each allowed by the policy over `L`. -/
def linesLang (pol : JsonLines.Policy) (L : Language UInt8) : Set (List (List UInt8)) :=
  {ls | ∀ l ∈ ls, l ∈ JsonLines.lineOf pol L}

end Json

end Silmaril.Wasm.Component.WIT
