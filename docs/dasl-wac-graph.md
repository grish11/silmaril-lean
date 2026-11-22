# WAC function-level compositions over DASL

`Silmaril.Wasm.Wac.Dasl` uses the existing WAC `Graph`, `Inst`, `Src`, `PkgSig`,
`FuncTy` and memory-free `ValTy`, not the separate source AST (`Wac.Text`) or
the elaboration and validation machinery (`Wac.Valid`). `Composition` adds an
ordered table of package interfaces and binary references. Indices denote table
rows or earlier instance nodes, as in `Graph`. `Composition.Resolved` adds a
package-index range check to the existing `Graph.WF`; decoding alone does not
establish it. In particular, `Graph.WF` checks resolution of consumed sources,
not type agreement or the validity of every possible extra argument.

## Schema: `wac/graph/v1`

The root is `["wac/graph/v1", [graph, packages]]`.

| Row | DASL representation |
| --- | --- |
| Graph | `[imports, [instances, exports]]` |
| Instance | `[package-index, arguments]` |
| Import source | `["import", name]` |
| Instance source | `["instance", node-index, export-name]` |
| Argument or export | `[name, source]` |
| Interface entry | `[name, [parameter-types, result-types]]` |
| Package | `[[imports, exports], raw-blob-link]` |

Collections are ordered arrays; indices are shortest unsigned decimal strings
with no I64 truncation. ABI scalar types are strings, records are arrays starting
with `"record"`, and variants are arrays starting with `"variant"`, with `null`
only for payload-free cases. The metadata is inline and cannot hide additional
CAS edges. Each binary slot requires the raw kind, not an object link even if a
store could decode that object. A root name identifies the object block; it is
not part of the encoded graph. Both names are abstract in the library codec.

## Checked contract

- `shallow.recovers` and `expanded.recovers` recover the whole composition. The
  expanded result adds the bytes without losing their raw names.
- `expansion_iff` and `full_iff` characterize finite expansion of a writer image
  exactly: the root binding and the specified raw byte binding for each package
  row. This requires no object-link recursion below the root. A repeated raw
  name must have compatible bytes in a binding store.
- `expandedNames_binding` gives one recovered composition per root in a binding
  store; it does not say that a composition has only one root name.
- The checked fixture wires two component binary ASTs (their emitted bytes parse
  as components), proves `Resolved`, and tests both complete and missing-blob
  stores. Its executable typed BDASL CBOR regression uses synthetic BLAKE3-shaped
  CIDs and tests raw/object classification and rejection by the SHA-256-only
  DASL profile.

No WAC grammar roundtrip, source declarations or aliases, WIT/world/resource
type elaboration, Wasm validation/execution, binary-to-signature attestation,
digest computation or content authentication is claimed. BDASL is exercised at
the fixture boundary, not assumed by the abstract name proofs.

```sh
lake build --wfail +Silmaril.Wasm.Wac.Dasl.Examples +Silmaril.Formats.Dasl.Wire.Thms
make check CHECK_TARGETS='+Silmaril.Wasm.Wac.Dasl.Examples +Silmaril.Formats.Dasl.Wire.Thms'
```

The examples are a leaf of the existing `Silmaril` Lake library, so the same
module is built by the repository's Lean CI.
