# Shared finite Prolly operations

`Silmaril.Semantics.Prolly.Operations.Thms` is the plain typed entry point. It
uses the existing `OrderedMap`, `Tree`, and `build`, without a DASL dependency
or a naming argument. `TypedMap` packages strict key order, valid separators,
nonempty branches and the width bound. A valid input need not have canonical
cuts. `TypedMap.combine` interprets both inputs and rebuilds the entire result
under the selected policy. The view/rebuild and commuting theorems describe
the operation extensionally; there is no incremental merge or locality bound.

`Silmaril.Semantics.OrderedMap.Operations.Thms` is enough for callers that need
only the finite carrier, including set operations (`Unit` payload). It
distinguishes domain subset from preservation of key/value pairs, and equates
cardinality with the size of the key domain. A combine visits the sorted union
of domains; shared keys alone call the overlap handler. The handler is a pure
`Except` function, and its first error stops evaluation. A successful `none`
drops a shared key. Left/right bias, rejection, and discard are ordinary
handlers. Discard means symmetric difference for union and an empty result
for intersection; rejection succeeds exactly for disjoint domains. Lookup
characterizes every output, and carrier recovery does not involve wire names.

The key type supplies its equality and order. In a later link-keyed profile
the default is identity of the typed name, not equality of decoded contents.
Two names for one payload are not automatically aliases in these operations.
Rekeying that identifies distinct names is not a transport of this algorithm:
it requires its own conflict and ordering policy. The generic carrier does
not establish nameless-to-named lifting, even if a key encoding emits a link.

## Shallow store operations

`Silmaril.Formats.Dasl.Prolly.Operations.Thms` reuses the checked Prolly scan,
block codec and publisher. `acquire` verifies the entire structural tree before
returning an ordered map. Given a valid typed AST, readable structural blocks
(`WholeReads`) and fuel greater than its level, the result is its exact view.
Any successful scan agrees with every binding reference that includes the
reader's positive observations and stores the input AST. Both facts hold for
valid noncanonical layouts too. Domain, cardinality, and contained-entry
queries can be run on the acquired map; there is no absence result when
acquisition encounters missing bytes, bad wire, an invalid node or low fuel.

`RootProfile.combineAndPublish` acquires both inputs left-to-right, applies the
carrier operation, rebuilds the result, and uses the collision-safe byte
publisher. Sound success gives the interpreted operation result, its fixed
profile root, the exact union of bytes, and structural readback. Publication
uses one authoritative snapshot, not a concurrent store. `ValidRoots` requires
canonical cuts, every reached block named by the selected profile, and a store
representation; successful publication witnesses that root in the decoded
object view. If such a root exists it is the unique member of the valid name
set for this profile. Binding neither supplies a naming witness nor makes
equivalent values have the same name across different profiles.

The object-link fixture uses the existing `objectLink` codec with a selected
name order; even missing link targets do not prevent name-keyed set algebra.
This is structural closure of the Prolly blocks, not full DASL resolution.
There is no new named-lifting theorem, alias collapse, or authenticated hash
implementation here.
