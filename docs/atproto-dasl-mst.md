# ATProto MST node codec and local checker

This is the node format from the [ATProto repository specification](https://atproto.com/specs/repository#mst-structure), separate from Prolly. The
[codec](../Silmaril/Formats/Dasl/Mst/Thms.lean) uses exactly the `e` and `l`
node fields and the `k`, `p`, `t`, and `v` entry fields. `l` and `t` are
object links or null, and `v` is an object link to the record. `k` is an
inline byte suffix. `p` is nonnegative within the signed i64 profile. There
is no extra key, raw link, ignored field, or replacement on error.

Prefix lengths are maximal common byte-prefix lengths, starting at zero for
the first key. Compressing then expanding recovers the node; successful
expansion also recompresses to exactly the supplied compressed node. The
DASL encoder/decoder recover every successfully encoded node. These are
shallow-AST checks, not new canonical-CBOR roundtrip claims. Node bindings
are a relational pushforward of shallow object bindings; the partial
decoder preserves binding.

[Local validation](../Silmaril/Formats/Dasl/Mst/Defs.lean) checks nonempty keys in
strict unsigned byte order, exclusive context bounds, one layer for all entries,
no children at layer zero, and the empty-root/intermediate-node distinction.
The [ATProto specialization](../Silmaril/Formats/Dasl/Mst/Atproto/Thms.lean)
uses the repository SHA-256 and counts leading zero two-bit groups (at most
128). The generic local checker does not import the hash. Successful reads
carry local validity; missing inputs, invalid wire, and invalid nodes remain
different outcomes.

## Rooted routing

[The routed model](../Silmaril/Formats/Dasl/Mst/Route/Thms.lean) divides each
node into singleton records and exclusive child gaps. Child contexts retain
the inherited bounds where no key cuts them, and descend one layer. Checked
strict node order implies the slots have disjoint domains. A finite `Realizes`
witness in the reference relation checks the contexts and bounds each subtree
within its slot; the in-order list is the strictly ordered concatenation of the slots. Null
slots contribute no entries. This is a rooted semantic witness, not a claim
that validating one wire node supplies the witness.

The routing checker uses only the selected path. Its found and absent answers
agree with every binding shallow-object extension containing that rooted
witness and the successful reads. A selected name must be decoded; missing,
invalid wire, invalid node, and exhausted fuel are kept separate. A record hit
returns the record name, not the contents of that object. The generic layer
function can be instantiated with `Atproto.keyLayer`.

## Not Yet Checked

- Repository path grammar and record values are not validated by the node
  format. A valid local node does not imply it has a valid global completion.
- Prove that a canonical builder produces the finite witness (including
  pruning and root maximality), and prove
  sufficient-fuel completeness for a full reader. Canonical building and
  collision-safe MST publications are separate from the routing result.

```sh
lake build --wfail +Silmaril.Formats.Dasl.Mst.Thms +Silmaril.Formats.Dasl.Mst.Atproto.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslMst.lean
lake build --wfail +Silmaril.Formats.Dasl.Mst.Route.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslMstRoute.lean
```
