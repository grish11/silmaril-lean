# Proper and dotted S-expressions over DASL

This is a decoded DASL schema over `Formats.SExp Atom` (proper lists) and
`Formats.SExp2 Atom` (cons, nil, and atoms), not a new Lisp grammar. Atoms use an
application-supplied `Encode.TotalCodec Atom ByteArray`. Identity bytes and UTF-8
strings are provided. Payload bytes are opaque, including bytes with a CID-shaped
prefix; an atom never doubles as a link.

| Profile | Atom | Empty | Nonempty |
| --- | --- | --- | --- |
| Proper | `{"sexp:atom": bytes}` | `[]` | array of children |
| Dotted array | `{"sexp:atom": bytes}` | `null` | `[car, cdr]` |
| Dotted dict | `{"sexp:atom": bytes}` | `null` | `{"car": car, "cdr": cdr}` |

The caller selects a profile out of band. An array of length two is not a reliable
profile discriminator. A database or viewer should retain the profile and the atom
codec identifier separately from the block name, and show syntax paths (zero-based,
nearest ancestor first; car is `0`, cdr is `1`) separately from CAS names.

## Placement and names

The root is always inline and may itself be stored as an object. An object edge
is allowed only at a syntactic child, and at most one wrapper is read there. A
child may be inline or linked; this includes atomic children and the dotted tail.
`linkAll`, `properNonAtoms`/`dottedNonAtoms`, and `inlineAll` select the three
normal forms. Nil counts as a non-atom in dotted syntax. No root, child, or digest
names are allocated by this library. A linked normal form fixes a caller-supplied
name choice in addition to its placement policy.

- `Proper.read_write`, `Dotted.read_write`, and `normalize_write` apply to every
  placement and hence to each normal form. `Dotted.transcode_write` works in both
  directions and can also change the placement. This is equality of recovered
  data / re-encoded images, not equality of the original blocks or their names.
- An unresolved syntax edge blocks recovery. `read_mono` says a successful
  partial recovery survives refinement. With a binding store and finite full
  expansion, `observations_agree` identifies the recoverable partial observation
  relation with recovery from the full view. `full_of_bindings` gives a finite
  expansion for any supplied expanded tree whose root and asserted bindings are
  present. It does not publish blocks or make an incompatible allocation valid.
- `Names` is the relation from root names to recovered syntax to use for a PER
  pullback. One name has at most one meaning in a binding store; multiple names
  may recover the same expression. With full expansions, `aliases_iff_normalize`
  identifies syntax aliases exactly with **successful** equal normalization by
  one fixed recoverable writer. Two failures are not aliases, and comparisons
  across independently chosen payload codecs or name allocators are not claimed.

## Logic and tooling boundary

The optional `Silmaril.ProofFormats.DaslSExp` adapter reuses a logic's existing
`Logic.Concrete.SExpCodec` (including the HOL and MLTT grammars on main) over its
actual `Logic.Smt.SE` carrier. It preserves decoded syntax and does not reimplement
the logic. The earlier HOL/MLTT DASL profile used bare string atoms and kept a
grammar-selected inline prefix; that profile's blocks are not wire-compatible
with the boxed atoms here. Callers may keep grammar-selected slots inline with a
custom `Placement`. No logic judgments, PER bridge, database or viewer are added
by this slice.

```sh
lake build --wfail +Silmaril.Formats.Dasl.SExp.Examples +Silmaril.ProofFormats.DaslSExp.Thms
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.SExp.Examples +Silmaril.ProofFormats.DaslSExp.Thms'
```

The examples (three placements, aliasing with two names, missing children, and a
dotted tail in both layouts) are a leaf of the existing `Silmaril` Lake library
and build in the repository's Lean CI. This is not a byte-level Lisp serializer,
a wire compatibility claim, or a proof that CID allocation is collision-free.
