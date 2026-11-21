# Sparse bitmap pages

The fixed geometry is one byte per occupied page, with a caller-selected
number of usable bits from 1 through 8. A bit has coordinates `(UInt64, Fin n)`:
the first coordinate is an unsigned page identifier, the second is the offset
from the least significant bit, and `n` is the selected number of usable bits.
The geometry is external to the block; readers and writers must agree on it.

The [layout](../Silmaril/Formats/Dasl/SparseBitmap/Defs.lean) is a sorted list
of nonempty pages, ordered by unsigned page identifier. Normalization of raw
pages ignores high padding bits, unions duplicate page identifiers, and omits
pages without usable bits. In contrast, the wire reader rejects empty pages,
nonzero padding, duplicates, descending identifiers, and masks of the wrong
length. A wire entry is `[i64 bits, one-byte string]`; the signed DASL integer
carries the identifier's bit pattern, not its unsigned numerical order.

The [API](../Silmaril/Formats/Dasl/SparseBitmap/Thms.lean) proves equivalence
with finite sets of bit coordinates, extensional normalization, membership,
cardinality as the sum of usable set bits, and shallow codec recovery. Page
count measures occupied pages, not semantic cardinality or serialized size.
Lookup uses the ordered list's lookup operation; no runtime or hierarchical
index bound is claimed. The same shallow codec can be used with either wire
profile; a root name additionally needs the profile's serialization, name
eligibility, store presence, and addressing coherence assumptions.

```sh
lake build --wfail +Silmaril.Formats.Dasl.SparseBitmap.Thms +Silmaril.Formats.Dasl.Wire.Profile.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslSparseBitmap.lean
```
