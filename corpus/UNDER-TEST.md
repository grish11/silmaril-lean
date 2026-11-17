# Source under test

Everything under `corpus/<pkg>/upstream/` and `corpus/<pkg>/generated/`, and the ELF files under
`corpus/elf/`, is **software under test**. It is not part of silmaril-lean:

* `upstream/` holds third-party releases, byte-for-byte as their authors published them
  (`upstream.sha256`, the archive hashes in `package.toml`). They are kept under their own licences
  (`NOTICES/corpus`), are never edited here, and are never built into silmaril-lean's tools or
  library. silmaril-lean's code does not include or link them. They are inputs whose builds the
  Lean development reads and states facts about.
* `generated/` holds files those packages' own build systems generated.
* `elf/` holds the build outputs.

Code-scanning alerts in these trees are findings about the upstream software, such as OpenSSL
implementing DES, RC2 or RC4, or integer-width patterns in its C. Alerts are kept visible rather
than dismissed, because a finding about software under test is information about that software.
They are not defects of silmaril-lean and are fixed, if at all, upstream.

silmaril-lean's own code in `corpus/` is the scripts at its top level (`build-all.sh`, `common.sh`,
`twin.sh`, `funcmap.py`, `tv.py`, `pp.sh`, `frontend.py`, …), each package's `fetch.sh`, `build.sh`,
`test.sh`, `package.toml` and `local/`, and the generated reports (`DECOMP.md`, `TV.md`). It is
scanned and reviewed like the rest of the repository.
