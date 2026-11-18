# Actual preprocessed mimalloc source under test

`options.i` is the actual GCC saved preprocessed translation unit from the pinned image/build that reproduced canonical x86_64 mimalloc byte-for-byte. `definition.c` is its exact39-byte `mi_version` definition including the existing newline, at UTF8 byte offset296176. The body-only span is38 bytes; both hashes are recorded to distinguish the original extraction from the exact frontend input.

`source-binding.json` and deterministic compressed build log record the archive identity, upstream source hash, all compiler commands, flags/image identity and canonical ELF SHA256. The extra `-save-temps=obj` observation build produced the canonical ELF hash; no new clean-reproducibility repetition or timing measurement is claimed. Existing canonical reproducibility receipts remain authoritative. System-header licence texts accompany the preprocessed file; upstream mimalloc uses the existing [MIT licence](../../../../../../upstream/mimalloc-2.1.9/LICENSE).

The standalone definition contains only builtin int types and literal219: no free identifiers, global reads, calls, memory accesses or environment services. Lean checks its byte span against the actual TU, runs the actual frontend by compiled evaluation, and kernel checks its Ail-to-Core elaboration. The external GCC preprocessor/build provenance remains a trust boundary. This is source semantics for the pinned closed definition, not a successful frontend parse or semantic equivalence theorem for the complete translation unit or allocator.

These files are software under test, not repository-owned C implementation. No source finding is dismissed or scan disabled by this representation.
