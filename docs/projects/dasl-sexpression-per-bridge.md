# DASL S-expression recovery PER bridge

Import `Silmaril.Formats.Dasl.SExp.Bridge.Thms`. The bridge uses the
[optional-placement codecs](../dasl-sexpressions.md) and the existing
[inline proper presentation](dasl-format-presentations.md), not a new syntax.

| Carrier | Equivalence and support |
| --- | --- |
| A decoded DASL tree, possibly with opaque links | `presentationPER`: both reads succeed and return the same syntax |
| A fully expanded named tree | `namedPER`: the same PER pulled back through `Named.embed`; resolution does not imply successful decoding |
| A root name in a fixed binding store | `rootPER`: both roots have a finite full expansion that recovers the same syntax (`Names`, `Aliases`) |
| A root certified to have a finite full view | `observedPER`: the root PER restricted to `FullRoot`; for a refinement-monotone reader, `observed_rel` characterizes it by a common successful `Observes` result |

For the proper and dotted readers, `read_mono` supplies the observation
hypothesis. This does not make `PartialNames` functional or claim an arbitrary
observation provides a finite full view. None of these relations identifies
names inside constructor congruence, allocates names, or changes the store.

`presentation_rel_normalize` and `root_rel_normalize` characterize a related
pair by a common **successful** normalized shape, never by two equal failures.
Fix the reader (including profile/layout and atom payload) and one recoverable
writer (including placement and name policy). A shape or CID alone does not
identify the reader, writer, or atom profile.

## Checked transports

```text
proper linked, named, or partial tree -- Proper.read payload --> Option (SExp Atom)
              \                                            | map intoAbstract
               +--------- parseAbstract? ------------------> Option (codec atom).Abstract
                                                          back: bind fromAbstract?
```

`Proper.abstract_write` commutes for every #1386 placement;
`abstract_recover` and `abstract_per` recover the source read and preserve its
PER. `Proper.inline_write` gives actual DASL tree equality for the same boxed
byte payload, and `Proper.rivest_inline` compares identity bytes against the
Rivest presentation via `SExp.map Bytes.data`. The symbol target can recover
the same `String` syntax after UTF-8 reading, but its string-valued atom node
is not the boxed-byte node.

For both dotted layouts, `Dotted.readTree` maps successful reads through
`SExp2.equivTreeOption` to `Tree2 (Option Atom)`; `tree_recover` gives the inverse
on the result and `tree_per` preserves the PER, including improper tails. This is not a transport to `Tree2 Atom`
without a nil representation. `Dotted.properAbstract?` is a noncomputable
specification using the existing proper-subtype equivalence. It succeeds
exactly on recursively proper recovered data, as checked by
`proper_abstract_hit` and `proper_abstract_rejects_improper`. It cannot turn
an improper tail into an inline proper list.

## CSLib and guarded congruence

The pinned CSLib dependency exposes `Cslib.HasContext` and
`Cslib.LawfulCongruence` in `Cslib.Foundations.Syntax.Congruence`. Import
`Silmaril.Formats.PER.Congruence.CSLib.Thms` for the checked forward adapter:
`support_context_lawful` turns `Constructors.Closed` into CSLib's congruence
on `PER.supportSetoid`, for single-hole constructor frames with fixed supported
siblings and a guard that is enabled for **every** supported filler. These
restrictions make filling a total action in CSLib. Importing the adapter does
not install a global context or congruence instance.

There is no converse or closure/lattice identification: CSLib's context law
requires an equivalence and a total unary fill; it does not express two-sided
guards on arbitrary tuples, disabled intermediate fills, or the support made
by enabled nullaries. CSLib's separate `Language.LeftCongruence`,
`RightCongruence`, and `Congruence` are for ordinary word setoids and
concatenation; those are not used as a guarded PER implementation.
