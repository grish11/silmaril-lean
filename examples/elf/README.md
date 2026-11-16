# Pinned ELF files of the ELF reader

The files the per-part ELF reader (`Silmaril.Elf.Staged.Pinned.*`,
[docs/projects/elf-reader.md](../../docs/projects/elf-reader.md)) checks and the explorer's ELF
tab shows. The proofs trust only that the bytes are these files: every part is checked by the
kernel on the file's `include_bytes`.

| file | what | size | SHA-256 |
|---|---|---|---|
| `pinned/gnu-sha256sum` | GNU coreutils 9.4 `sha256sum`, `/usr/bin/sha256sum` of Ubuntu `coreutils` 9.4-3ubuntu6.3 (amd64), unmodified: a stripped x86-64 PIE, dynamically linked (glibc, OpenSSL `libcrypto`) | 39336 | `4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60` |
| `../dyn/pinned/hello-gcc` | hello world (`examples/dyn/hello/hello.c`), gcc 13.3 `-O2`, dynamically linked against glibc 2.39 (`PT_INTERP` `/lib64/ld-linux-x86-64.so.2`, `DT_NEEDED` `libc.so.6`); pinned and reproducible: [examples/dyn](../dyn/README.md) | 15960 | `6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7` |
| `../dyn/pinned/hello-clang` | the same hello world, clang 18.1 `-O2`, dynamically linked against glibc 2.39 (same interpreter and `DT_NEEDED`); pinned and reproducible as above | 16008 | `ecad1a19e6e63e4828e9386a9c831dc6beb635c6858dc42d2c248e6397eaa713` |

    examples/elf/pin.sh --check   # the committed files have the pinned SHA-256
    examples/elf/pin.sh --fetch   # download the Ubuntu package, check it, extract sha256sum

`--fetch` downloads `coreutils_9.4-3ubuntu6.3_amd64.deb` from Launchpad
(`https://launchpad.net/ubuntu/+archive/primary/+files/coreutils_9.4-3ubuntu6.3_amd64.deb`,
falling back to `archive.ubuntu.com`), checks its SHA-256
(`e1e9a17892be0cc83b7cea747edf331ffeb6d6c010b4db296e60d888e8e9274c`), extracts
`./usr/bin/sha256sum` and checks the file's SHA-256. It is the same file whose functions
`Silmaril.Elf.Effects.Example.Sha256sum` certifies (`NOTICES/effects-examples`).

`disasm/*.objdump` are the listings the explorer shows as **unverified** disassembly: GNU
objdump's output (`objdump -d -w -z FILE`; the first line records the objdump version), written by
`scripts/elf-reader/gen.sh`. Nothing in Lean is about them.

## Licence

GNU coreutils is licensed under the GNU General Public License, version 3 or (at your option) any
later version (`NOTICES/GPLv3`). The corresponding source of this binary is
https://launchpad.net/ubuntu/+source/coreutils/9.4-3ubuntu6.3 (and https://ftp.gnu.org/gnu/coreutils/);
see `NOTICES/effects-examples`. The file is redistributed unmodified.
