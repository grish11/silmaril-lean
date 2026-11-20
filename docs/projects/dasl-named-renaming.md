# Named DASL: renaming and indexed PERs

`Silmaril.Formats.Dasl.Renaming.Thms` puts a single function on the names
of the landed `Named` and `Partial` trees. It acts recursively, preserving
inline shape, indices, and object/blob tags. Erasure ignores the action;
taking a shallow view commutes with it. The action preserves the information
order `Extends`. This is not a theorem about sort keys: link-ordered collection
layouts may need to be re-normalized after a rename.

`Store.renameImage` sends object entries to the **renamed shallow targets**
and blob entries to the **same bytes**. It is monotone in source inclusion,
and observation commutes with it. `Renaming source target` requires this
image to be admitted by the target. It composes across name types, preserves
expansion, and transports validity when the target is binding. A noninjective
map is allowed only if the target admits the result; for a binding target
collapsed names in a lane must have identical *output* targets. The two lanes
are checked independently. To enforce codec domains, wire eligibility or hash
integrity, use target and source relations that already impose those policies;
renaming itself never computes or identifies content digests.

`Silmaril.Formats.Dasl.NamedPER.Thms` uses the existing `Formats.PER`, with
`onStore` restricting its support to trees whose witnesses are admitted by a
binding store. `Respects` is an explicit **forward** transport law for a source
and target PER. It composes, has identity, and yields a `PER.Map`, hence a map
of supported quotients. `Family.Equivariant` asks for that law uniformly between
binding stores. Pullbacks from nameless erasure satisfy it. Equality of shallow
views supplies a name-sensitive family that also satisfies it, but a
noninjective action may identify formerly distinct classes, so reflection
does not follow. A PER whose support singles out one spelling need not satisfy
even the forward law, including for an injective rename. Transport is separate
from the guarded constructor congruence of #1381 and from union-find.

The shallow family pulls back a partial-tree PER along `Named.embed`. An
opaque partial link carries a name, not a witnessed binding. Admitting a
partial tree does not require opaque links to exist or resolve in the store.

`lake build --wfail +Silmaril.Formats.Dasl.NamedPER.Examples` checks the
cross-type nested object/blob action, rejected byte collisions, alias collapse,
name-sensitive equivariance versus failure of reflection, non-equivariant
support, and an opaque partial link.
