# OpenSSL `libcrypto` byte ranges

The module `Silmaril.Elf.Link.Dyn.Sha256sum.Scope.Defs` contains short byte ranges (77 chunks,
2109 bytes in all: the ELF and program headers, the dynamic section, and the parts of the symbol,
string, version and GNU hash tables that symbol lookup reads for the references of GNU
`sha256sum`) of one file of OpenSSL 3.0.13 as packaged by Ubuntu (`libssl3t64`
3.0.13-0ubuntu3.16, amd64):

| file | size | sha256 |
|---|---|---|
| `libcrypto.so.3` | 5309400 | `6866ed711dab8927e1bf82bf1cd30e828bdfc34f3cc1e83b1c9eb01ce6c37d9a` |

OpenSSL 3.0 is licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0; a copy of the licence text is in
`NOTICES/Binaryen/LICENSE.txt`). Its source is the Ubuntu source package `openssl`
3.0.13-0ubuntu3.16 (https://launchpad.net/ubuntu/+source/openssl/3.0.13-0ubuntu3.16) and the
upstream release (https://www.openssl.org/source/). The byte ranges are stored unmodified; no
other part of the library is redistributed.
