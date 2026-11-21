# Partial equivalences on DASL

`Silmaril.Formats.PER` is the pre-semantic type on a carrier: its support is
`R.Dom a := R.rel a a`. Related endpoints are both supported. Its existing
`supportSetoid` is the ordinary equivalence on that subtype, and `ofSetoid`
and `toSetoid` bridge the case of total support. The pinned CSLib uses ordinary
Setoids (for example, for its left/right language congruences), which impose
reflexivity on their carrier. This development uses the repository's existing
PER and shared partial-equivalence laws instead of a second Setoid or PER.

- `WeaklyCompatible` agrees on pairs of valid values, but can relate valid
  and invalid values. `weak_counterexample` exhibits this on `Bool`.
- `StrictlyCompatible` preserves *original* validity along the extension's
  edges and agrees whenever one endpoint is originally valid. The extension
  can still have additional support disjoint from the old classes.
- `singletonCompletion` adds equality everywhere; distinct invalid values
  remain apart. `invalidCompletion` instead adds one class of all invalid
  values. These bound all strictly compatible total equivalences, and agree
  exactly when there is at most one invalid element.
- `NormalForm` is uniqueness only, ignoring unsupported selections;
  `SupportedNormalForm` additionally excludes those selections. Coverage is
  separate. `RelativeNormalForm` requires uniqueness modulo a second PER, not
  equality. Existing `Canonical` is equivalent to support inclusion,
  coverage, and the restricted relation being discrete on its support.

`PER.Constructors` is a polynomial algebra: one operation per shape, with a
shape-indexed set of positions and an explicit enable predicate on each child
tuple. A related pair of tuples may be composed only when both are enabled.
There is no ambient reflexivity rule. In particular, a nullary rule only adds
reflexivity when enabled. An empty signature is closed for
every PER. Arbitrary PER joins close the union; congruent PER joins further
close under the constructors. Neither closure inserts global reflexivity.

`Tree.Rules` is the direct presentation of those rules for actual DASL
`Tree`: dicts use the same finite key set and list pairs the same length;
objects require the same name; blob, reference, and scalar payloads are part
of the shape. It applies to `Value`, `Named`, `Partial`, `Mixed` and `Shallow`
by specializing the existing `Tree` parameters. The distinguished typeclass
signature enables every constructor, so a closed PER for that signature on a
free DASL tree has total support. For partial support, use explicit guards.

Mapping, erasing and taking a shallow projection transport the generated
relation forward when the seed and enable predicates transport. A projection
can forget names or payloads but supplies no converse that identifies them in
the source. `Constructors.upper` alone gives soundness in the *generated* PER;
only if the seed is closed is this soundness in the original PER.
`SyntaxCompatible` adds seed inclusion and reflexivity to the upper bound.
With a closed seed, it forces equality to the seed (and hence total support).

Local check:

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Congruence.Examples'
```
