# Git arena: exact lazy reads and backend adapters

The [Git arena](git-arena.md) now has an optional adapter for external byte
readers. Names and decoding stay independent of acquisition and storage.

| Adapter | Contract |
| --- | --- |
| `Reader.exact` / `State.cacheBytes` | For a nonresident claimed ID, decode the fetched bytes for that ID and require that the configured serializer returns those **exact** bytes in the same lane. Then run the existing checked materialization. Preserve missing, deferred, invalid and conflict. A resident hit does not call the reader. |
| `State.cacheAndAssign` | After successful intake, try to attach a name in another lane. A failed assignment leaves exactly the cached arena and returns the assignment fault separately. |
| `State.casReader` | Read bytes by CAS name and lane from an immutable arena snapshot. Never fall back to an OID or another lane. |
| `Descriptor.raw` / `Descriptor.object` and `Descriptor.read` | Pair a typed decoder with a CAS name and lane. Preserve every read failure; an unsuccessful decode is invalid, not missing. The descriptor contains no Git OID, slot, or evidence of binding. |

An exact intake is limited by the configured native/CAS serializer. A
permissive decoder recognizing another spelling does not let this adapter
substitute canonical bytes for the bytes fetched under the claimed name.
Exact bytes alone do not validate an OID; existing profile and coherence
checks still apply. Use the separate collision-policy index for policy-governed
queries and disputed native candidates, not this adapter as a bypass. The
adapter does not combine collision notice delivery and cache writes into a
transaction, and `deferred` and `missing` are not negative cache evidence.

`cacheBytes_spec` exposes the resident or verified-intake branch and exact
byte witness. `cacheAndAssign_spec` distinguishes committed intake from a
secondary naming failure. `cacheAndAssign_valid` preserves validity and
observation of the original binding; any successful derived name is also an
observed binding for that same payload. `cacheAndAssign_extends` preserves all
prior payloads, claims and kind hints. `descriptor_found` ties a typed arena read
to the observed binding, bytes and decoder result. None of these checks establishes
hash injectivity or validates an arbitrary external reader by parsing.

## Standalone filesystem consumer

Pure filesystem specs should import the landed
[resident Prolly contract](https://github.com/hiloopai/silmaril-lean/blob/65cacd11e2363738ccff97d241163b214ea4a1fd/docs/projects/arena-prolly-reads.md), **not** this Git
arena adapter. A directory CID remains whatever name type the filesystem
profile selects. Use `Dasl.Arena.Prolly.Reader Ref Key Item` (reference to
`Except (Dasl.Prolly.Fault Ref) (Semantics.Prolly.Block Ref Key Item)`) with
`Dasl.Prolly.route`. Keep raw bytes on a separate reader. A missing block is a
fault, never a successful route returning `none`; authenticated absence still
requires the rooted reference and separator assumptions in the Prolly API.

When an implementation elects to read from the Git arena, `CasReader.prolly`
supplies that same block-reader type from the **object** lane, a wire parser,
and a block codec. It leaves classification of arena-specific read failures
explicit because the current Prolly fault type cannot represent defer and
conflict separately. Keep the richer `Descriptor.read` results where callers
need those diagnostics. The adapter distinguishes wire from node decode
errors and requires a separate reference-binding premise for verified reads.
No layout, key order, codec tag, hashing, filesystem semantics, or production
mount implementation is chosen here.

```sh
lake build --wfail +Silmaril.Formats.Git.Arena.Reader.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitArenaReader.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Arena.Reader.Thms
```
