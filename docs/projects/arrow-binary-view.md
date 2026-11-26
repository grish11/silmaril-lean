# Arrow BinaryView and Utf8View slots

The little-endian slot reader takes the view buffer, the ordered variadic data
buffers, a physical slot index, and a per-value byte limit. The caller
identifies non-null slots. It handles the Arrow Columnar 1.5 view layout
introduced in 1.4. Array validity, IPC type dispatch and variadic buffer
count metadata are separate interfaces.
[Columnar layout, Arrow 26.0.1](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#variable-size-binary-view-layout)

`BinaryView.readBinary` checks the whole 16-byte slot and its signed length
before reading the payload. Values of at most 12 bytes are inline and their
padding must be zero. Longer values have a nonnegative buffer index and
offset, a bounded range inside the selected buffer, and a four-byte prefix
that must agree with the payload. References can overlap. The limit is
checked before slicing or UTF-8 decoding. `BinaryView.readUtf8` reads the
same payload and requires successful UTF-8 decoding.
[Definitions](../../Silmaril/Formats/Arrow/BinaryView/Defs.lean)

`readBinary_iff` characterizes the exact inline or referenced window.
`readBinary_extent` gives its well-formedness and exact bounded length.
`readUtf8_iff` adds the UTF-8 observation to the checked wire relation.
[Laws](../../Silmaril/Formats/Arrow/BinaryView/Thms.lean)

The fixture uses PyArrow 26.0.1 to concatenate views from two input arrays.
PyArrow's BinaryView and Utf8View buffers agree byte for byte. The compiled
Lean examples check the seven valid values, including an empty value, both
sides of the inline boundary and both data buffers. Additional guards cover
overlap, short carriers, malformed signed words, range and prefix errors,
and invalid UTF-8. The pinned Linux x86-64 PyArrow wheel has SHA-256
`7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814`.
[Generator and buffer hashes](../../scripts/arrow-binary-view/fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/BinaryView/Examples.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.BinaryView.Thms +Silmaril.Formats.Arrow.BinaryView.Examples
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-binary-view/Axioms.lean
python3 -I scripts/arrow-binary-view/fixtures.py --regenerate
```
