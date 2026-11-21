# String-to-DASL object map

The [flat layout](../Silmaril/Formats/Dasl/StringObjectMap/Defs.lean) uses a
strictly ordered `OrderedMap String (Placement Name)` and encodes entries as
`[key, placement]` pairs. Ordering is Lean `String` order on decoded keys;
this is an array, not a DRISL dictionary. A placement is either
`["inline", object]` or `["link", object-link]`. The explicit tag matters: an
inline object's root may itself be a link. The linked placement rejects blob
links and recovers one stored shallow object. It does not recursively resolve
links within that object.

The [flat theorems](../Silmaril/Formats/Dasl/StringObjectMap/Thms.lean) give
extensional equality by placement lookup, cardinality as the size of the
key set, and shallow codec recovery. Different placements can recover the
same object: there is no claim that two such maps are equal, or have the same
name. Choosing placements and addresses canonically is a separate policy.

The [index adapter](../Silmaril/Formats/Dasl/StringObjectMap/Index/Thms.lean)
instantiates the existing Prolly builder, block codec and **closed-view scan**
with text keys and the same placement codec. With stored canonical index
blocks, a binding reference store, and a sound reader, successful lookup
returns exactly a shallow value allowed by the map (or proves key absence).
Missing and invalid index blocks or value bytes remain distinct failures.
This is neither a routed lookup nor a performance claim. The reader takes
the chosen wire parser and object guard; it neither chooses the profile's
digest algorithm nor verifies hashes.

```sh
lake build --wfail +Silmaril.Formats.Dasl.StringObjectMap.Index.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslStringObjectMap.lean
```
