# Cambridge ASTs as UTF-8 JSON

Import `Silmaril.Courses.Cambridge.AstCodec.JsonBytes` and apply
`AstCodec.JsonBytes.codec` to a Cambridge constructor-tree codec such as
`L1.Codec.termSExp`. The result is a `TotalCodec` whose target is
`Silmaril.Formats.Bytes`. The bridge uses the same version-1 envelopes,
constructor arrays and string atoms as the existing JSON value schema.
The same bridge accepts resolved codecs such as
`L3.ResolvedCodec.termSExp`.
[Cambridge AST schema](cambridge-ast-codecs.md)

```lean
import Silmaril.Courses.Cambridge.AstCodec.JsonBytes
import Silmaril.Courses.Cambridge.L1.Codec

open Silmaril.Courses.Cambridge
def l1JsonBytes := AstCodec.JsonBytes.codec L1.Codec.termSExp
```

## Exact output

The encoder writes compact JSON using the library's deterministic
printer. It uses lowercase `\uXXXX` escapes for each UTF-16 code unit,
including a pair for a supplementary character. For example, the string
value `"a😀"` is emitted as the exact UTF-8 bytes of
`"\u0061\ud83d\ude00"`.

`decode_encode` recovers an AST from its emitted bytes.
`reencode_canonical` shows that decoding and then re-encoding those
bytes recovers the same byte string. `text_of_encode` recovers the exact
printed string by decoding the output as UTF-8. These laws compose the
existing structural AST round-trip with the checked adapter to the JSON
wire tree and the library's `JsonWire.parse_encode` byte theorem.
[JSON wire proof](../../Silmaril/Formats/JsonWire/Encoding/Thms.lean)

## External JSON

The decoder runs the complete RFC 8259 reader before checking the AST
schema. External JSON can use whitespace, literal Unicode, and alternative
valid string escapes. `decode_of_parse` proves that any input parsed to the
same wire tree as an encoded AST decodes to that AST. Re-encoding selects
the canonical spelling. Whitespace and escape choices in external input
are discarded.

The schema admits arrays and scalar-Unicode strings only. It rejects
objects, JSON numbers and other scalar kinds. Numbers in AST fields retain
their existing decimal-string rules. The adapter rejects unpaired
surrogates even though the underlying RFC reader preserves those code
units. Invalid UTF-8 and trailing data fail the wire parser. JSONC comments
and JSON5 syntax are outside this reader's dialect.
[JSON wire reader](../../Silmaril/Formats/JsonWire/Defs.lean)

```sh
lake build --wfail +Silmaril.Courses.Cambridge.AstCodec.JsonBytes.Examples
```
