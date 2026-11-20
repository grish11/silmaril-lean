# DRISL debug JSON and simple trees

This is a debug interchange layer, not canonical JSON and not full AT Protocol
record or Lexicon validation. It is independent of the fast JSON parser and
chunk representation. Standards: [DRISL](https://dasl.ing/drisl.html), [DASL
CID](https://dasl.ing/cid.html), [BDASL](https://dasl.ing/bdasl.html), [AT
Protocol Data Model](https://atproto.com/specs/data-model), [RFC
8259](https://www.rfc-editor.org/rfc/rfc8259), [RFC
8949](https://www.rfc-editor.org/rfc/rfc8949), and [RFC
4648](https://www.rfc-editor.org/rfc/rfc4648). Artifact pins for the CBOR and
DRISL profiles are in `references.bib`.

## Shared API

- `Silmaril.Formats.JsonWithBytes.Defs`: `Scalar Number` has null, bool, Unicode
  scalar string, number, and bytes (`List UInt8`). `Ordered` reuses the indexed
  `RawSyn` tree (arrays and objects in document order, including duplicates).
  `Unordered` reuses `Json` (finite maps), and `Sorted` is its string-ordered
  representative. `OrderedI64` and `UnorderedI64` use `Int64`; the default number
  is `JsonWire.Decimal` (coefficient, exponent, sign, including negative zero).
  Use `RawSyn.toJson` with `WellFormed` to forget member order and `Json.toOrdered`
  to choose a representative. Wire parsers reject duplicate names, including
  equivalent Unicode escape spellings, and reject lone surrogate escapes.
- `Silmaril.Formats.Cbor.Drisl.Ast.Defs`: `Ordered Link` and
  `OrderedATProto Link` add links through `Scalar.data`/`Scalar.link` and share
  all non-link leaves. `Cid .any` is the default; use `Cid .dasl` / `Cid .bdasl`
  or supply a `CidCodec` for a custom fixed-layout implementation. `any`
  validates shortest unsigned varints, CIDv1 and the exact digest boundary;
  it permits arbitrary codec and multihash *numbers*, not unsupported CID
  versions or arbitrary tag-42 bytes. It does not consult a registry or check
  content/digest integrity. `foldLinks` visits links in document order with no
  intermediate leaf list. The fast representation can cache link absence or
  share link-free subtrees; no such cache, layout, or benchmark is specified
  here. Do not split the shared scalar schema into bytes/no-bytes variants.
- The AST header provides `embedI64`. `Convert/Defs.lean` has `removeLinks?`,
  `widenATProto` / `narrowATProto?`, `fromJsonWithBytes?` / `toJsonWithBytes?`, `jsonWithBytesI64?`,
  and `recodeLinks?` for fixed/any CID conversions. `Convert/Thms.lean`
  characterizes the link-free ATProto trees exactly as the image of `embedI64`.

## Debug format

The reserved wrappers are singleton objects `{"$bytes":"…"}` and
`{"$link":"…"}`. The link key is singular; `$links` has no special meaning.
Bytes use standard unpadded base64 (ATProto permits optional padding; this
debug reader picks one spelling). Links use lowercase base32 without padding
and with the multibase `b` prefix. Reserved singletons with malformed payloads
fail; they never fall back to ordinary objects. An empty byte string is
`{"$bytes":""}`.

| Ordinary key | No escape | Suffix one dollar | Prefix one dollar |
| --- | --- | --- | --- |
| empty string | `""` | `""` | `""` |
| `$` | `$` | `$$` | `$$` |
| `$bytes` | `$bytes` | `$bytes$` | `$$bytes` |
| `$$link` | `$$link` | `$$link$` | `$$$link` |

Choose the policy out of band. An escaped reader accepts only canonical
escapes for ordinary dollar-prefixed keys, recursively. Escapes are removed
exactly once. In no-escape mode, the round-trip domain excludes any ordinary
object that is a reserved singleton, anywhere in the tree. Multi-field objects
with reserved names are legal in that mode; treating no-escape mode as
unrestricted injective encoding would be wrong. Member order is preserved in
the debug tree, and the unordered i64 law compares finite-map semantics.

DRISL integers have the two CBOR argument ranges, `[-2^64, 2^64-1]`; ATProto
uses signed 64-bit integers only. DRISL stores exact binary64 bits (finite,
excluding negative zero). Debug JSON prints a double as its *exact* decimal,
using a negative decimal exponent chosen from its binary exponent field. It
prints integers with exponent zero. Thus `1` the integer, `1.0` the DRISL
double and adjacent representable doubles are not collapsed by the paired
debug codec. A JSON consumer that normalizes numeric tokens or parses numbers
through native doubles cannot be expected to preserve this distinction. Exact
subnormal spellings can be large; this is not a shortest-decimal printer.
General JSON-with-bytes renders its input decimal unchanged in the exact
decimal model. Lowering that model to DRISL prefers integers and fails on
out-of-range integers, negative zero, and fractional decimals not exactly
representable as binary64. It does not round (`0.5` succeeds; `0.1` fails).

`Debug/Text/Defs.lean` uses the existing RFC JSON reader/printer; the text
languages additionally enforce Unicode, wrapper, number and duplicate rules.
`JsonWire.parse_encode` recovers the exact ordered wire AST from printer bytes,
including UTF-16 code units and exact decimal fields. `Debug.ofWire_toWire`
then recovers the scalar-Unicode debug tree. The byte-level left inverse in
`Debug/Text/Thms.lean` applies to every duplicate-free tree in either escaped
policy. No-escape additionally requires `CollisionFree .none`. The image
right inverse is for printer outputs, not arbitrary accepted JSON spellings.
The printers agree byte-for-byte on the overlapping DRISL/ATProto/i64 profiles
and across escape policies on trees without dollar-prefixed object names.
`Model/Defs.lean` interprets CBOR values separately from bytes. Canonical bytes
must decode as one complete item, reproduce the input bytes on deterministic
re-encoding, and have strict bytewise order of encoded keys. The CBOR value
reader accepts any order of unique keys. `Model/Thms.lean` relates the byte
language to this interpretation and the CBOR reader. `renderJsonWithBytesCbor?`
checks DRISL representability; `parseJsonWithBytesCbor?` lifts link-free DRISL
into exact decimals. The latter accepts, for example, integral doubles; the
preferred integer-first lowering is not an inverse for their CBOR kind.
The CBOR theorems characterize the accepted bytes via the existing decoder and
the value model; they do not prove that the canonical writer and reader are
inverses or identify the model byte language with the older `Drisl.language`
profiles. A writer/reader law would compare against recursively sorted object
members (or an order-insensitive view), since the writer sorts map keys.

### Compatibility with the named CBOR languages

`Model/Thms.lean` proves byte-language equality for DRISL with either exact
DASL or exact BDASL CIDs and for the signed-i64, no-float ATProto core with
either CID rule. The proof compares the two real readers on every decoded
item; `Cbor.encodable_of_decode` supplies the head and size bounds and strict
encoded-key ordering rules out duplicate decoded names.

These equalities are for exact boundaries and the corresponding link rules:
the legacy CID-prefix reader accepts a digest followed by an extra byte,
which the exact reader rejects. Conversely, the default `.any` reader can
accept a canonical two-byte CID codec varint that neither fixed rule accepts.
The legacy “no floats” profile alone is not ATProto: it still accepts the
unsigned argument `2^63`. The theorem header checks these distinctions.

For all three built-in CID profiles, rendering any successful DRISL or ATProto
read returns the original bytes. Reading after rendering preserves the exact
ordered AST if its unsorted CBOR emission is encodable and already has strictly
ordered keys throughout; these guards do not assume any parser equality.
Exact AST recovery without the order guard is false: the writer sorts `b, a`
to `a, b`. The general writer is partial, and arbitrary caller-supplied
numeric/CID codecs are not assumed to be inverses. No theorem about equality
modulo key order for arbitrary input order is claimed here.

Run the targeted checks with:

```sh
lake build --wfail +Silmaril.Formats.Cbor.Drisl.Debug.Text.Thms +Silmaril.Formats.Cbor.Drisl.Model.Thms
lake env lean -DwarningAsError=true --run tests/formats/DrislDebug.lean
```
