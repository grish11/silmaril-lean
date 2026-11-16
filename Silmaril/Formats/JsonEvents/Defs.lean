module

public import Silmaril.Semantics.StreamBounds.Defs

/-!
# JSON event streams and JSON trees

A JSON value seen as a stream is a sequence of *events*: scalars, `beginArray`, `endArray`,
`beginObject`, `key k`, `endObject`, in document order. This is the shape streaming readers
(SAX- or pull-style) produce. It is also the semantic interface for component interfaces
that pass JSON as a sequence of variant cases. This module fixes the event type, the tree
type, the encoding of a tree as events, and a decoder.

* `Tree K S`: an ordered JSON tree with keys `K` and scalars `S`. Arrays are lists. Objects
  are *lists of members*, so member order and duplicate keys are kept, as on the wire
  (RFC 8259 §4 leaves duplicates to the receiver). This is the shape of
  `Silmaril.Formats.JsonWire`'s AST; the extensional `Silmaril.Formats.Json`, which forbids
  duplicates and forgets order, is a quotient of it.
* `Event K S`: the event alphabet. A key event precedes each member value.
* `Tree.toEvents`: the encoding. `language K S` is its range, the well-formed event streams.
* `ofEvents?`: the decoder, with fuel bounded by the stream length (`Thms`: it inverts
  `toEvents`, so `Tree K S` and `language K S` are in bijection).
* `Event.kind`: `beginArray`/`beginObject` open, `endArray`/`endObject` close, the rest are
  neutral. The generic `Silmaril.Streams.DepthBound Event.kind d` on event streams is the
  format-specific depth `Tree.depth` (`Thms`), which is the depth of `JsonBytes.ValueAt`.

The scalar and key types are parameters. A JSON reader instantiates them: for example `K`
the decoded string (`String`, or UTF-16 code units if lone surrogates are kept) and `S` a sum
of `null`, booleans, number lexemes and strings. Choosing them, and relating the events of a
byte text to `Silmaril.Formats.JsonBytes.language`, is not done here. No lexer from bytes to
events is defined or proved.
-/

@[expose] public section

namespace Silmaril.Formats.JsonEvents

universe u v

/-- An ordered JSON tree: arrays and member lists keep order and duplicates. -/
inductive Tree (K : Type u) (S : Type v) where
  | scalar (s : S)
  | array (items : List (Tree K S))
  | object (members : List (K × Tree K S))
  deriving Repr

/-- The events of a streamed JSON value. -/
inductive Event (K : Type u) (S : Type v) where
  | scalar (s : S)
  | beginArray
  | endArray
  | beginObject
  /-- The name of the next member of the enclosing object. -/
  | key (k : K)
  | endObject
  deriving DecidableEq, Repr

variable {K : Type u} {S : Type v}

/-- How an event changes the nesting depth. -/
def Event.kind : Event K S → Silmaril.Streams.BracketKind
  | .beginArray | .beginObject => .opening
  | .endArray | .endObject => .closing
  | _ => .neutral

mutual

/-- The events of a tree, in document order. -/
def Tree.toEvents : Tree K S → List (Event K S)
  | .scalar s => [.scalar s]
  | .array items => .beginArray :: itemsEvents items ++ [.endArray]
  | .object members => .beginObject :: membersEvents members ++ [.endObject]

/-- The events of array items. -/
def itemsEvents : List (Tree K S) → List (Event K S)
  | [] => []
  | t :: ts => t.toEvents ++ itemsEvents ts

/-- The events of object members: each key, then its value. -/
def membersEvents : List (K × Tree K S) → List (Event K S)
  | [] => []
  | (k, t) :: ms => .key k :: t.toEvents ++ membersEvents ms

end

mutual

/-- Nesting depth: scalars `0`; an array or object `1 +` its deepest child. -/
def Tree.depth : Tree K S → Nat
  | .scalar _ => 0
  | .array items => itemsDepth items + 1
  | .object members => membersDepth members + 1

/-- The deepest item. -/
def itemsDepth : List (Tree K S) → Nat
  | [] => 0
  | t :: ts => max t.depth (itemsDepth ts)

/-- The deepest member value. -/
def membersDepth : List (K × Tree K S) → Nat
  | [] => 0
  | (_, t) :: ms => max t.depth (membersDepth ms)

end

/-- The well-formed event streams: those that encode a tree. -/
def language (K : Type u) (S : Type v) : Language (Event K S) := {es | ∃ t : Tree K S, t.toEvents = es}

mutual

/-- Read one value, with fuel. -/
def parseValue : Nat → List (Event K S) → Option (Tree K S × List (Event K S))
  | _ + 1, .scalar s :: r => some (.scalar s, r)
  | n + 1, .beginArray :: r => (parseItems n r).map fun p => (.array p.1, p.2)
  | n + 1, .beginObject :: r => (parseMembers n r).map fun p => (.object p.1, p.2)
  | _, _ => none

/-- Read array items up to and including `endArray`, with fuel. -/
def parseItems : Nat → List (Event K S) → Option (List (Tree K S) × List (Event K S))
  | 0, _ => none
  | _ + 1, .endArray :: r => some ([], r)
  | n + 1, es => (parseValue n es).bind fun p =>
      (parseItems n p.2).map fun q => (p.1 :: q.1, q.2)

/-- Read object members up to and including `endObject`, with fuel. -/
def parseMembers : Nat → List (Event K S) → Option (List (K × Tree K S) × List (Event K S))
  | _ + 1, .endObject :: r => some ([], r)
  | n + 1, .key k :: r => (parseValue n r).bind fun p =>
      (parseMembers n p.2).map fun q => ((k, p.1) :: q.1, q.2)
  | _, _ => none

end

/-- Decode a complete event stream to a tree. -/
def ofEvents? (es : List (Event K S)) : Option (Tree K S) :=
  match parseValue (2 * es.length + 1) es with
  | some (t, []) => some t
  | _ => none

end Silmaril.Formats.JsonEvents

end
