# Exact dictionary-free Zstandard frames with Huffman literals

`CheckedFrame.Huffman.decode` reads one standard frame from a caller-bounded
input. It uses the checked header, exact block extents and trailer from
`CheckedFrame`. Type-2 blocks use `CompressedBlock.Huffman.decode` for
raw, RLE, new-tree and treeless literal sections and the checked sequence
modes. Each block receives the remaining frame output budget and the
previous accepted history, repeat offsets, Huffman table and sequence
tables. Physical raw and RLE blocks add their output to rolling history
while preserving both tables and repeat offsets. [RFC 8878 frame format][rfc]

`readBlock_sound` ties each output and accepted successor to the original
three-byte header, exact body and untouched suffix. `plain_state` proves
both table identities and repeat-offset preservation for physical raw
and RLE. `block_history` identifies the next history as the last window
of prior history and block output. `readBlocks_sound` accounts for the
remaining output budget and assembles output chunks in wire order
through the first last-block flag. `decode_sound` ties the chain to the
original dictionary-free header and establishes the caller's input,
output and window limits. It also proves the declared content size
when present and the exact trailer, which is the four-byte low XXH64
checksum when enabled and empty otherwise. [Theorem header][thms]

The profile rejects nonzero dictionary IDs, skippable frames, reserved
block types and bytes after the verified frame, including a second frame.
Treeless literals or Repeat sequence tables require checked prior state
in the same frame. The logical bounds govern sizes and command count.
The profile uses `distance < Window_Size`; pinned libzstd accepts the
equality fixture, whereas both implementations accept the distance one
below. The earlier frame APIs keep their existing profiles. Parquet
codec activation is separate. [Strict-window differential][window]

## Verification

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-frame-oracle/check.py
```

The differential builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It pins frame, block and
output SHA-256 hashes and compares complete output bytes. The original
level-3 pair and its native checksummed version contain a four-stream
new direct tree followed by a single treeless stream. The checksummed
interposition fixture keeps the compressed bodies and inserts physical
raw and RLE blocks between them. Its expected output and checksum come
from independent libzstd calls on the resulting frame. The oracle also
covers a checksummed frame without declared content size, a native
single-stream FSE-weight frame and both sides of the strict window rule.
[Pinned manifest][fixtures] · [Native library][zstd]

Both implementations reject the corrupted sequence marker, bad or
truncated checksum, wrong declared size, truncated extent, trailing byte,
nonzero dictionary ID, reserved block type and cold treeless fixture.
The exact Lean profile separately rejects concatenated and skippable
inputs that libzstd accepts and enforces one-less input, output, window and
command caps. The runner checks that failures publish no output.
[Oracle runner][oracle]

[rfc]: https://www.rfc-editor.org/rfc/rfc8878.html#section-3.1.1
[thms]: ../../Silmaril/Formats/Compression/Zstd/CheckedFrame/Huffman/Thms.lean
[window]: zstd-sequence-frame.md#window-boundary
[fixtures]: ../../scripts/zstd-huffman-frame-oracle/fixtures.json
[oracle]: ../../scripts/zstd-huffman-frame-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
