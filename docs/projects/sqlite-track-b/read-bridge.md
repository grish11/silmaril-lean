# SQLite Track B designated-leaf read

The bridge relates the packed leaf decoded from a designated SQLite page to
the height-zero case of the generic numbered-page B-tree. Its input is a
`File.View`, caller-selected page number, and `Int64` rowid. Track A
supplies the page-relative B-tree header offset and the VDBE read kernel.

## Representation and lookup

`leaf` uses the bindings of the admitted `Vdbe.Table` in their original
pointer order, with signed `Int` keys and full VDBE rows. `leaf_valid`
derives strict key order from the packed decoder's guard and proves that
record decoding preserves those keys. `leaf_represents` puts those exact
bindings in the generic `BTreePages.PageData.leaf` at the SQLite page number.
The height-zero tree has just one reachable path and the abstract memory
has just one defined slot.

`page_lookup_run_iff` specializes the generic `BTreePages.lookup_run_iff`.
The generic `Page.Run` returns the full matching row or a miss, keeps the
memory, and emits no edits. `leaf_lookup` relates its result to Track A's
`lookupValue` using signed key conversion, the table's existing get law,
and the VM's projection of column one, counting from zero. The direct
`lookupLeaf` agrees with both `seekLeaf` and `runLeaf`, including decode
rejection. [Bridge definitions](../../../Silmaril/Machine/SQLite/TrackB/Read/Defs.lean) ·
[Public theorems](../../../Silmaril/Machine/SQLite/TrackB/Read/Thms.lean)

## Direct Pager seam

The staged runner calls the existing `PageRead.Acquire.acquire` and passes
the copied byte view to the direct B-tree consumer via Track A's
`finishAcquire`. `run_eq_staged` and `run_eq_composed` equate the entire
outcomes for any handler, including the result or ordinary error, actual
file and cache poststates, and completed VFS exchanges.

`finishAcquire_page` starts from a successful acquisition and admission
of its exact bytes at the designated offset. It produces a generic run
whose projected result gives the staged consumer's result, with the full
acquisition observation. `readOnly_cold_warm_page` supplies that bridge
for a read-only snapshot. The file bytes must match the image, the page
lookup must supply the designated view, the handle and read range must
be valid, the slot must be owned and vacant, and the original view must
decode. The cold read installs precisely the bytes used to obtain the
represented leaf and records one complete read. The warm read starts
from the returned file and cache and records zero exchanges. The theorem
validates the actual concatenated trace. [Track A read contract](../sqlite-track-a/read-case.md)

The generic page-memory model starts at the admitted leaf payload. Acquisition
and decode errors stay in Track A's `Except ReadError` channel, while generic
UB and divergence are `Page.Exit.stopped` outcomes. The admitted bridge
covers 512-byte packed rowid leaves in the decoder's local two-field record
profile. It assumes the caller has already designated the page and opened
the handle. Native C semantics or equivalence, writes, locks, WAL, traversal
of interior pages, and SQL-level equivalence are outside the model.

## Typed Pager and VFS observations

`handledPager_returns_run` interprets Track A's `pagerTree` with
`pagerHandler backing` for a supplied backing handler and initial file
and cache. The returned value is the whole Track B outcome. At that
boundary the acquisition step is silent and all completed VFS exchanges
are in the returned payload, including exchanges with ordinary errors.

`handledPager_returns_page` requires a successful acquisition by that same
handler and admission of the bytes actually supplied. It constructs the
generic `Page.Run` and shows that projecting its returned row yields the
typed Pager result with the actual file, cache, and exchanges.

`vfsTree_observes_run` selects the finite observation of Track A's open
`vfsTree` using the supplied handler's replies. Its visible exchanges are
`vfsExchanges` of that handler's completed VFS trace, and its return is
the result and cache. Other well-typed replies can produce other
observations. The theorem gives membership for the handler-selected
path.

`readOnly_cold_warm_observations` specializes to the same read-only
snapshot premises as the direct theorem. The cold and warm typed Pager
returns project the same generic Page run on the installed bytes. At the
VFS boundary the cold path exposes the complete read and the warm path
has no exchanges. The combined trace validates the actual read-only file
transition. [Typed bridge theorems](../../../Silmaril/Machine/SQLite/TrackB/Read/Interaction/Thms.lean) ·
[Track A typed adapter](../sqlite-track-a/read-interaction.md)

## Dependency revisions and checks

- The abstract B-tree and Page calculus landed in [#3520](https://github.com/hiloopai/silmaril-lean/commit/36be0bff05ebe9d29244c65de72d0988a2162da2)
  and [#3534](https://github.com/hiloopai/silmaril-lean/commit/d684648f10d2786026116b66072374876bd5b201).
- The exact Track A read seam comes from [#3555 at 852fe2dc](https://github.com/hiloopai/silmaril-lean/commit/852fe2dcb8628565856abe1074273abd96ce27ff).
- The generalized Track B representation and lookup theorem use [#3558 at 9de63c03](https://github.com/hiloopai/silmaril-lean/commit/9de63c03bb4981f1cf9649398c37195487e210e1).
  Its six files match the [landed revision](https://github.com/hiloopai/silmaril-lean/commit/c688d55edaad3bfab248e5cd309282116f96127c).
- The typed Track A seam uses [#3572 at b71f7df5](https://github.com/hiloopai/silmaril-lean/commit/b71f7df50b00679ab5e3784ba694621d54731920)
  and the [#3543 interaction foundation at 61d4a44f](https://github.com/hiloopai/silmaril-lean/commit/61d4a44f4514730e0779c4180a768abc21086ed7).

`Checks.lean` encodes and parses a two-row image, checks the signed ordered
bindings, and exercises a negative-rowid hit, a miss, and a short read.
It also constructs the generic hit and miss runs for the same leaf payload,
and prints the transitive axioms of the bridge theorems.
The typed checks prove a short read from the read-only handler produces
an ordinary acquisition error in both observations. The handled Pager
returns the exchange in its payload and the VFS observation exposes it
as a visible request/reply pair.
[Direct checks](../../../Silmaril/Machine/SQLite/TrackB/Read/Checks.lean) ·
[Typed checks](../../../Silmaril/Machine/SQLite/TrackB/Read/Interaction/Checks.lean)

```sh
targets='+Silmaril.Semantics.BTreePages.Checks
+Silmaril.Machine.SQLite.TrackA.Read.Interaction.Checks
+Silmaril.Machine.SQLite.TrackB.Read.Checks
+Silmaril.Machine.SQLite.TrackB.Read.Interaction.Checks'
lake build --wfail $targets
make check CHECK_TARGETS="$(echo $targets)"
for checks in Silmaril/Machine/SQLite/TrackB/Read/Checks.lean \
    Silmaril/Machine/SQLite/TrackB/Read/Interaction/Checks.lean; do
  lake env lean -DautoImplicit=false -DwarningAsError=true "$checks" || exit 1
done
```

The pinned kernel replay driver can also recheck the bridge declarations
against their imports.

```sh
for module in Silmaril.Machine.SQLite.TrackB.Read.Defs \
    Silmaril.Proofs.Machine.SQLite.TrackB.Read.Correctness \
    Silmaril.Machine.SQLite.TrackB.Read.Thms \
    Silmaril.Proofs.Machine.SQLite.TrackB.Read.Interaction \
    Silmaril.Machine.SQLite.TrackB.Read.Interaction.Thms; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean || exit 1
done
```
