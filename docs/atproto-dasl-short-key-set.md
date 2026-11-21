# Short byte and UTF-8 key sets

Both [key types](../Silmaril/Formats/Dasl/ShortKeySet/Defs.lean) have a caller
selected bound from 0 to 255 **bytes**, inclusive. Empty keys are allowed.
Byte keys use unsigned lexicographic order. Text keys use Lean `String` order,
with exact UTF-8 recovery and no Unicode normalization or case folding.

The [codecs](../Silmaril/Formats/Dasl/ShortKeySet/Thms.lean) offer a DASL array
of byte or text values, or a single inline DASL byte string. The latter uses
project-local framing: one unsigned length octet per key followed by exactly
that number of bytes. For packed text each key must decode as valid UTF-8.
Both readers check strict order and reject duplicates of the recovered keys;
the packed reader also rejects truncated or oversized keys. Successful
unpacking re-encodes to exactly the original octets. The payload size
of the packed representation is exactly the sum of key byte lengths plus one
byte per key, before the enclosing wire header. No performance claim is made.

The layout is equivalent to `Finset` of bounded keys. The proofs give
extensional normalization, membership, cardinality, and recovery for all
four shallow codecs. Pick the array or packed layout before naming an object;
the two layouts are not asserted to produce the same bytes or names.

```sh
lake build --wfail +Silmaril.Formats.Dasl.ShortKeySet.Thms +Silmaril.Formats.Dasl.Wire.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslShortKeySet.lean
```
