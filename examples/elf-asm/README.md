# Assembly functions as JSON (`silmaril.elf.asm/1`)

`zlib-checksums.json` is written by `tools/elf-asm` from `Silmaril.Elf.Asm.Example` and the checked
theorems of `Silmaril.Elf.Asm.Example.Thms` ([docs/projects/elf-asm.md](../../docs/projects/elf-asm.md)):
four functions of `examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums` (zlib, see
`LICENSE.zlib` there) and one function claimed for an unmodelled machine.

```
lake build elf-asm
lake env .lake/build/bin/elf-asm examples/elf-asm/zlib-checksums.json          # regenerate
lake env .lake/build/bin/elf-asm --check examples/elf-asm/zlib-checksums.json  # compare (make elf-check)
```

Each function's `evidence` is read from theorem statements; `lines` are `objdump -d` text (display
only); `decodings` are the instruction models' decodings with `Repr` renderings.
