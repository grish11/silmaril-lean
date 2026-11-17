# glibc byte ranges

The modules `Silmaril.Elf.Link.Dyn.Glibc.Defs`, `Silmaril.Elf.Link.Dyn.Small.Libc`,
`Silmaril.Elf.Link.Dyn.Program.Glibc` and `Silmaril.Elf.Link.Dyn.Program.StdExe.Bins.Glibc`
contain short byte ranges (a few kilobytes in all: the ELF and program headers, the dynamic
section, and the parts of the symbol, string, version and GNU hash tables that symbol lookup reads)
of two files of the GNU C Library 2.39 as packaged by Ubuntu (`libc6` 2.39-0ubuntu8.9, amd64):

| file | size | sha256 |
|---|---|---|
| `libc.so.6` | 2129424 | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |
| `ld-linux-x86-64.so.2` | 236616 | `c20a2dc8917c755f02b94049356320fe1f62ac7d9f8994731f807d9df39302da` |

The GNU C Library is free software, licensed under the GNU Lesser General Public License,
version 2.1 or (at your option) any later version (https://www.gnu.org/licenses/lgpl-2.1.html).
Its complete corresponding source is the Ubuntu source package `glibc` 2.39-0ubuntu8.9
(https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9) and the upstream release
(https://ftp.gnu.org/gnu/glibc/glibc-2.39.tar.xz).

The executables in `examples/dyn/pinned/` contain glibc's crt start-up objects (LGPL-2.1-or-later
with the linking exception) and GCC's `crtbeginS.o`/`crtendS.o` (GPL-3.0-or-later with the GCC
Runtime Library Exception); see `examples/dyn/README.md`.

## Whole files: `examples/elf/pinned/glibc-libc.so.6` and `glibc-libm.so.6`

`libc.so.6` (sha256 above) and `libm.so.6` (952616 bytes, sha256
`fce00b6f25f459cf4ae0b7fae4257909a1a8a86f9149e7c029a5d617baf1ccd0`) of the same package are
redistributed unmodified, whole, for the ELF reader and the explorer's function tables
(`Silmaril.Elf.Staged.Pinned.{GlibcLibc,GlibcLibm}`, `examples/elf/README.md`;
`examples/elf/pin.sh --fetch` downloads and checks them). They are under the licence above; the
complete corresponding source is the Ubuntu source package and upstream release named above.

## Whole file: `examples/elf/pinned/glibc-2.36-libm.so.6` (Debian 12)

`libm.so.6` of the GNU C Library 2.36 as packaged by Debian 12 (bookworm), `libc6`
2.36-9+deb12u14 (amd64), member `./lib/x86_64-linux-gnu/libm.so.6` (911904 bytes, sha256
`7f2ca87f652f56b094462474b076749e90e689d0ecb9cb63c7679820b271b4e7`), is redistributed
unmodified, whole. It is the `libm.so.6` of the container image
`silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9`, the
image whose `/usr/include/math.h` (package `libc6-dev` 2.36-9+deb12u14) is the pinned header
import `examples/headers/clang/glibc-math.json`: header and binary come from one glibc build. It
is read by `Silmaril.Elf.Staged.Pinned.GlibcLibm236` and the libm conformance rows
(`Silmaril.Elf.Abi.Libm`); `examples/elf/pin.sh --fetch` downloads the package
(`libc6_2.36-9+deb12u14_amd64.deb`, sha256
`ba4f88f73dbc3ae9055f3c20f4523bfdbaf1ad13ff95e258924f77d20b4fbedf`, from
https://snapshot.debian.org/archive/debian/20260504T025922Z/pool/main/g/glibc/) and checks the
package and the file.

The file is licensed under the GNU Lesser General Public License, version 2.1 or (at your
option) any later version (https://www.gnu.org/licenses/lgpl-2.1.html); see the package's
`/usr/share/doc/libc6/copyright`. Its complete corresponding source is the Debian source package
`glibc` 2.36-9+deb12u14
(https://snapshot.debian.org/package/glibc/2.36-9%2Bdeb12u14/, https://sources.debian.org/src/glibc/2.36-9+deb12u14/)
and the upstream release (https://ftp.gnu.org/gnu/glibc/glibc-2.36.tar.xz).
