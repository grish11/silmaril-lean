# Ordered DASL file inodes

`FileInode` models a UnixFS-inspired file DAG, not the UnixFS protocol. In this
layout the root is an inode object, and the tagged shallow DASL object
`["file-v1", [[link, length], ...]]` lists child spans in byte order. An object
link points to another inode; a blob link points to raw bytes. A child length
is a positive signed i64; offsets and sums are unbounded natural numbers. The
empty inode encodes an empty file. Limits bound fanout and page size separately.
There is no prescribed packing, balance, metadata, CID assignment, or unique
layout for a file's contents.

`Resolves` specifies a full file in a snapshot without referring to the range
reader. Each finite depth witness validates every child and every declared
length. `resolves_length` and `prefix_length` identify the total byte count and
every declared child start offset with those of the recovered bytes.

`read` accepts exact half-open ranges specified as `(offset, count)` (`none`
recovers the entire file). It uses child lengths to skip disjoint spans without
fetching their targets, checks the size of every visited node, and permits a
zero-length read at EOF. Missing, invalid wire/layout, exhausted depth fuel,
and a range exceeding the declared root length are distinct errors. A success
does not certify that a partial snapshot has a valid completion. `range_sound`
and `recover_sound` instead apply to **every** such completion agreeing on
successful observations. `range_complete` and `recover_complete` give exact
results in the full snapshot when fuel covers the depth witness.

The DASL and BDASL snapshot adapters use the common wire profile and require the
matching object/raw CID kind. These are syntax checks; callers supply bindings
and any integrity checks. No SHA-256 or BLAKE3 computation is required by the
proofs. There is no claim of UnixFS interoperability.

```sh
lake build --wfail Silmaril.Formats.Dasl.FileInode.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslFileInode.lean
```
