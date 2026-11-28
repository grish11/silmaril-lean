# Pinned-Go dictionary profiles

`Silmaril.Languages.Starlark.Lists.GoDictionary.Thms` exposes a separate
executable dictionary profile. `Bucket.empty` and `set` build an eight-slot
table with no deletion. `get` computes the query hash and selects the probe
candidates from the occupied slots. Keys and values use the existing heap
carriers. Tuple key fields must remain immutable for the lifetime of the
table. The resolved interpreter continues to use its canonical key cache.
[Definitions](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Defs.lean) · [Canonical profile](starlark-lists.md#dictionary-membership-and-lookup-profiles)

## Hashing

Keys in this profile are `None`, Booleans, integers, binary64 values and
nested tuples of those values. The integer hash uses the low 32 bits of the
signed value in the int32 range and of the magnitude outside it. The
binary64 path reuses the exact decoder. It applies Go's signed int64
conversion in range and rational division outside that range. Go hashes
infinities and NaNs to one constant. Tuples mix the raw field hashes, with
all arithmetic in 32 bits. The table reserves zero only after the whole key
has been hashed. A heap-sized bound on tuple reads admits the finite acyclic
keys of this profile and terminates on a malformed graph.
[Pinned integer hash][int-hash] · [Pinned float conversion][float-int] · [Pinned float hash][float-hash] · [Pinned tuple mixer][tuple-hash]

`intHash_toNat` states the modular formula. `hashesAt_iff` connects
successful executable hashing to independent field and mixer rules,
including binary64 decoding. The fixtures compare 25 exact raw hash words
with pinned Go, including signed int32 boundaries, a large negative integer,
fractional and out-of-int64 floats, and two unequal deep tuple keys with the
same hash.
[Theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Checks.lean) · [Go oracle](../../scripts/starlark/go-dictionary/check.go)

## Slots and observations

The occupied suffix represents slots in ascending order. Insertion uses
the highest vacant slot. A probe compares only entries with the normalized
query hash, using the default depth for each reached key comparison.
`candidates_slots` identifies that traversal with filtering the physical
slots. `set_hit_slots` and `set_miss_slots` give the exact slot update after
a hit or a miss with room. A hit names a live row and replacement keeps its
key and hash. Iteration follows the reverse of occupied slot order, so
writing through an equivalent key preserves its displayed key and position.
A miss at capacity is a profile rejection. Go grows its table on that path.
[Pinned slot insertion][insert] · [Pinned lookup][lookup] · [Ordered agreement](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Thms.lean)

`looksUp_iff` proves exact raw lookup agreement with the independent hash
and ordered probe premises. Both `contains` and `equalWith` use that
lookup and observe a reached key-depth error as a miss. Excluded keys and
malformed model reads retain their errors. Outer dictionary equality checks
size and walks the left insertion order, passing the remaining depth to the
supplied value comparator. A deep key collision can produce a raw error
before the cyclic value is reached. The paired fixtures exercise this case.
[Pinned membership][membership] · [Pinned dictionary equality][equality] · [Lean fixtures](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Checks.lean)

## Growth and overflow chains

`GoDictionary.Growth.Thms` exposes a table starting at one bucket. Its
width is a power of two. Go hashes the query once, selects a home with the
32-bit mask, and walks the primary bucket and overflow links in ascending
slot order. It compares only matching full stored hashes. An error aborts
the insertion, and a hit replaces the value in place. Only a miss tests
overload. The exact predicate is at least eight entries and twice the entry
count at least thirteen times the bucket count. This is Go's 6.5 load test
on representable counts and power-of-two widths. The first thresholds are
eight, thirteen, and twenty-six entries. After doubling, the old count
always leaves room for the retried insert.
[Pinned insertion][insert] · [Pinned overload and rehash][grow]

The model derives each home chain from the chronological rows. A new entry
takes the last vacant slot in that chain. When every slot is occupied, the
first entry of a new overflow block goes in slot zero. Later entries fill
that block from its last slot down. `slots_wellFormed` proves the occupied
slots form a permutation of the indexed home rows and gives the exact
number of eight-slot blocks. The append theorems give the slot updates and
`probe_slots_iff` connects the executable probe to independent ordered
rules for hits, misses, and first reached comparison errors.
[Growth definitions](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Defs.lean) · [Growth theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Thms.lean)

Go rehashes in linked insertion order, recomputing each stored key's hash.
For every chronological prefix, `home_double` identifies the new home as
the old home's stable subsequence under the wider mask. `candidates_double`
lays out that subsequence before selecting full-hash matches. The second
split can change the order of collisions by moving an entry from overflow
back into the primary bucket. An exhausted miss still transfers between
widths because it already tested every matching hash and each test returned
false. Errors reached before overload propagate, and lookups after growth
follow the new slot order.
[Pinned rehash][grow] · [Growth theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Thms.lean)

`Replayable` records stable hashes and the comparisons required for
successful replay. Each later key must miss every earlier key with the
same stored hash. It holds for an empty table and successful inserts and
replacements preserve it in a fixed key heap. `reinserts_of_replayable`
gives the replay steps from any permitted prefix, and `reinserts_double`
lifts them to the wider mask. `rehash_run` proves that replay from an empty
wider table returns the exact widened table with the original stored
keys, values, and chronological order. `set_grow` connects this layout
to the overloaded miss and its retry.
[Growth theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Thms.lean)

The paired controls cover the second rehash, multiple overflow links, and
the reordered same-hash candidates when a different hash moves to the other
home. Ordinary numeric keys check iteration order and key identity after
float alias replacement. Oracle-only trace keys observe the actual probe
order and hash recomputation. The depth controls exercise errors at both
thresholds and verify that equality treats a reached lookup error as a miss
before comparing a cyclic value after the second rehash.
[Growth fixtures](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Checks.lean) · [Go fixture](../../scripts/starlark/go-dictionary/check.go)

The profiles assume an unfrozen table without active iterators and stable
tuple key reads. The mathematical layout and replay proofs quantify over
every power-of-two width. Go correspondence assumes successful allocation
and representable Go widths and entry counts.

## Deletion and slot reuse

`GoDictionary.Deletion.Thms` exposes the standalone table with stable slot
addresses. The slot map stores rows, the insertion list links those same
addresses, and the overflow counts retain allocated chains. `WellFormed`
ties the two views together. Every occupied slot belongs to the correct
home, is within its allocated chain, and appears exactly once in the
insertion list. Every linked address is occupied. The live count stays
within the width's load threshold.
[Definitions](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Deletion/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Deletion/Thms.lean)

Delete hashes the key and scans the selected chain in ascending slot order,
testing the full-hash candidates until the first match or comparison
error. A hit clears that one cell, returns its previous value, and unlinks
the same address. All surviving slots, stored keys, and chronological
positions relative to one another are preserved. Empty overflow links stay
allocated. The linked list is represented by its addresses in order.
`deletes_iff` proves exact agreement with the independent ordered rules,
including the unchanged table on a miss and the raw error on failure.
`unlink_candidates` shows that every post-delete probe sees the old order
with the cleared address removed. Membership and dictionary equality still
observe a reached key-depth failure as a miss.
[Pinned deletion][delete] · [Delete rules](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Deletion/Operational/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Deletion/Thms.lean)

A later insert checks overload after its initial probe, using the live
count. With room it fills the highest vacant slot anywhere in the selected
chain, or allocates a new link at slot zero when the chain is full. Each
new key goes at the tail of the insertion list, including a key reinserted
through an alias. A replacement updates only its existing value.
`delete_replayable` preserves the stable-hash, pairwise-miss invariant
because surviving rows form a subsequence. `grow_replay` uses the
width-parametric replay rules to reconstruct the exact widened table from
an empty slot map, with survivor order and key identity preserved. The
retry uses the survivor candidates in their rebuilt physical order.
[Pinned insertion][insert] · [Pinned rehash][grow] · [Theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Deletion/Thms.lean)

The paired controls cover primary and overflow holes, reuse of an empty
retained link, alias reinsertion, and a second rehash with holes still
present. The Go guard controls confirm that freeze and active iteration
reject deletion before hashing, and that a never-initialized Go dictionary
returns a miss before hashing. The admitted profile starts with an
initialized table, as with `NewDict(0)`, and requires an unfrozen table
without active iterators. Mutable key reads, process-dependent string
hashing, callable keys, recursive Go-profile values, and canonical
interpreter integration remain separate.
[Pinned mutability guards][guards] · [Lean controls](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Deletion/Checks.lean) · [Go controls](../../scripts/starlark/go-dictionary/check.go)

## Agreement with canonical dictionary operations

`GoDictionary.Abstraction.Thms` connects the explicit-slot table to the
canonical list of entries. The relation ties each live slot to one cached
entry at the same insertion position. It preserves the original key and
value, including a float's stored bits. The proof uses well-formed slots,
stable replayable rows, and unique canonical codes. The resolved
interpreter continues to use the canonical backend.
[Abstraction definitions](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Abstraction/Defs.lean) · [Canonical coverage](starlark-lists.md#dictionary-membership-and-lookup-profiles)

A coherent key profile validates each admitted key with both
`State.keyOf` and the pinned hash. Equal codes imply equal stored hashes.
Comparisons between candidates sharing a full hash are total and return
exactly the code test. `lookup_agrees` then selects the same full entry or
miss in both tables. The hash narrows the physical search, and the unique
canonical code identifies the result regardless of slot order. All scalar
keys satisfy these laws in any heap. The pinned scalar hash factors through
the canonical code, including signed zero, equal integers and floats,
NaNs, and infinities. Booleans retain their own code.
[Abstraction theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Abstraction/Thms.lean)

`set_agrees` relates both branches of physical assignment to
`putEntry`. A hit keeps the stored key and position. An insert appends
the key, including when it first rehashes the table. `readDict_agrees`
gives the canonical subscript value or missing-key error and its unchanged
state. `writeDict_agrees` gives the exact canonical cell update and
relates the successor tables when the key observations stay coherent.
Scalar coherence holds before and after any such update. The paired
controls cover same-hash integers, both rehashes, numeric values around
2^53, and alias replacement through negative zero and a different NaN
payload.
[Lean controls](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Abstraction/Checks.lean) · [Pinned Go controls](../../scripts/starlark/go-dictionary/check.go)

The physical rules still preserve the first reached error. In the
separating control the canonical cache hits a ten-level tuple alias and
misses an unequal tuple with the same stored hash. Physical lookup reaches
a depth error in both cases, and Go membership observes a miss. The
coherence proof for other tuple families needs stable agreement between
cached codes and live fields, as well as a bound that makes every reached
collision comparison total.
[Paired depth controls](../../scripts/starlark/go-dictionary/check.go) · [Lean controls](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Abstraction/Checks.lean)

The read theorem permits frozen cells. The successful-write theorem
assumes a live unfrozen dictionary and no active iterator on its address.
The guard bridge below extends this result to rejected writes. Changing
key reads across writes requires a stability proof. Strings need the
pinned short-string hash and a stable seed for longer keys. Functions and
builtins need identity and hash laws covering their names and bound
receivers.
[Pinned mutability guards][guards] · [Pinned string hashing][string-hash] · [Pinned function hash][function-hash] · [Pinned builtin hash][builtin-hash]

## Mutation guards and allocation

`GoDictionary.Guards.Thms` adds a stateful wrapper for assignment and
direct deletion. A freeze flag and an active iterator count gate both
operations before hashing. Freeze wins when both guards apply.
`guard_agrees` proves the exact canonical write error and the unchanged
state on both sides. The canonical error carries the receiver address.
The Go wrapper observes the guard reason, and the oracle checks Go's
operation-specific error text. Entering an iterator preserves the
relation. A frozen Go dictionary leaves its count alone while the
canonical loop pushes the address. The shared guard still observes
freeze. Go iterator lifetime and shared-store execution remain separate
from this wrapper's mutation proofs.
[Pinned mutability guards][guards] · [Pinned iterator entry][go-iterators] · [Guard theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Guards/Thms.lean)

A zero-value Go dictionary has no allocated buckets and can represent a
live empty canonical cell. After the guards pass, Go assignment allocates
storage before hashing, so even a hash error leaves the empty buckets
allocated. A rejected guard leaves allocation and rows intact. Direct
deletion of unallocated storage misses before hashing. Direct deletion
of initialized empty storage hashes, and a reached hash error leaves
that table intact. The direct-delete proof also lifts the exact removed
value and state of an admitted deletion. Go's `popitem` checks emptiness
before calling `Delete`, and a frozen empty dictionary reports
`popitem: empty dict`.
[Pinned assignment][insert] · [Pinned deletion][delete] · [Pinned popitem][go-popitem]

`writeDict_lockstep` covers scalar insertion and replacement, including
initialization, and classifies shared unhashable list, dictionary and
range keys. Canonical key validation reports `unhashableKey`, and the
standalone hash reports `unsupportedKey` for those carriers. The paired
outcome records the exact state on each side. An uninitialized canonical
binding fails while evaluating the receiver, and a missing canonical
heap cell reports its address error. These failures are separate from
Go's zero-value dictionary. Canonical display insertion checks key and
duplicate entries before calling its cell edit. Its raw helper can
therefore report a key error on a frozen receiver. Actual displays
construct their own dictionary and follow a separate evaluation rule.
[Canonical coverage](starlark-lists.md#dictionary-mutation-guards) · [Pinned display instruction][go-display]

The denotation theorem starts the physical mutation after right-hand
side, receiver and key evaluation, in that order. A key-expression
error precedes the guards. Earlier effects are retained at the state
reached by the failing operand or guard. Both fixtures exercise keys
that fail if hashing or encoding is reached. The Go controls record
operand and hash calls, and the Lean controls observe allocation effects
retained on rejection. Canonical and standalone backends remain separate.
Tuple cache stability, strings and callable keys remain outside the
guard bridge.
[Pinned RHS compilation][go-assignment] · [Pinned target compilation][go-assignment-target] · [Pinned subscript instruction][go-setindex] · [Lean controls](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Guards/Checks.lean) · [Go controls](../../scripts/starlark/go-dictionary/check.go)

## Reproduction

```sh
lake build --wfail +Silmaril.Languages.Starlark.Lists.GoDictionary.Checks \
  +Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Checks \
  +Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Checks \
  +Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Checks \
  +Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Checks
fixture="$(pwd)/scripts/starlark/go-dictionary/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

[int-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/int.go#L183-L193
[float-int]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/int.go#L447-L462
[float-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L476-L491
[tuple-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1186-L1199
[insert]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L78-L150
[grow]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L153-L175
[delete]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L285-L330
[guards]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L332-L340
[lookup]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L177-L201
[membership]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1030-L1048
[equality]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L921-L951
[string-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L430-L450
[function-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L759-L765
[builtin-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L832-L851
[go-iterators]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L393-L427
[go-popitem]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L1273-L1288
[go-display]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L469-L487
[go-assignment]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1093-L1098
[go-assignment-target]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1265-L1273
[go-setindex]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L427-L436
