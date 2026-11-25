# ABI-side xRead and the owned page-fill contract

`MatchesPage binding req page` ties the file pointer of an abstract
`SqliteRead.Request` to the page's VFS handle and equates the physical
page offset and size to the ABI transfer fields. The caller supplies the
binding for the backing under consideration. `page_admitted` adds the
one-based page number premise and derives PageRead admission from the
existing ABI context.
[Binding and statements](../../Silmaril/Machine/SqliteVfs/PageRead/ReadBoundary/Thms.lean) ·
[ABI-side contract](../../Silmaril/Machine/SqliteRead/Defs.lean)

`returning_handler_agrees_with_fill` assumes ABI admission, including the
context's exclusive ownership of the destination span, an abstract live
handle and a vacant owned slot. It also assumes the returning handler law
against the same file byte snapshot.

- A full result agrees byte-for-byte with the exact VFS reply and fills
  the slot with those bytes.
- A short result agrees byte-for-byte, including the zero-filled suffix.
  The VFS exchange records the short response and the slot remains vacant.
- Other raw status codes retain the original outside-buffer frame.
  The theorem leaves their abstract result and in-span bytes unspecified.

The full and short conclusions give the file state, cache and typed
singleton exchange of the existing read-only fill. The buffer frame
describes the caller-visible buffer view. A future concrete result needs
to supply the pointer binding, establish the memory ownership, and prove
that the chosen native handler returns with the assumed ABI-side law.
The pinned dispatch proof ends at handler entry.
[Owned page fill](sqlite-page-read.md) · [Pinned dispatch cut](sqlite-vfs-read.md)

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Checks
```

The kernel fixtures use a two-byte request with a full and a short
modeled response, plus the frame for another raw error code. They use
concrete ABI fields, binding and buffer views.
[Checks](../../Silmaril/Machine/SqliteVfs/PageRead/ReadBoundary/Checks.lean)
