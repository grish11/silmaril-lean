# Actual native BoringSSL no-asm/asm followups

This tranche adds18 actual pinned BoringSSL native ELF rows: no-asm O2, asm O0,
asm O2, each libcrypto/libssl/bssl unstripped and stripped. The original six no-asm
O0 rows are a separate prior tranche. [summary.json](summary.json) links each
profile's exact receipts, hashes, source inventories, census, stripping maps and
actual timings. All source/output/module/provenance hashes, both repeats' runtime
records and54 measured exits passed independent verification.

Independent clean builds and independent strips match bytes. Both repeats and
forms passed SHA256/AES known answers, Ed25519 acceptance/rejection, certificate
signature/TLS1.3 BIO handshake/application transfer and bssl observations.
Runtime FIPS_mode=0 for all these non-FIPS configurations. Supplementary BCM ET_REL
preserves actual upstream fipsmodule objects via explicitly repository-authored
ld-r packaging; it is not upstream FIPS_SHARED bcm.o, stays unstripped and is not
counted among the18 library/executable rows. No FIPS validation/certification.

Sources are public upstream commit ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6 under
test, archive75ee588268ae3d7552f5be7e0849bdcc8e4159f22547dbfb4aae997784fdd345.
Licenses/notices, upstream pregenerated assembly and public generators/build
inputs are preserved. Asm profiles compile upstream committed pregenerated lists;
no local perlasm regeneration is claimed. No-asm preserves available assembly
as provenance only. C volatile-inlineasm syntax remains separate lexical evidence,
not active preprocessing/execution or compiler-emitted assembly.

The same two independently initialized extended-image workers are reused with
private source/build/temp/home/shared-memory workspaces reset each profile.
Complete220-package lock (all210 base versions unchanged), tool hashes and15659-file
Go-tree inventory were verified independently in both workers. These are reused
container/workspace repeats, not per-profile new-container repeats. Exact commands,
flags/source/recipe/tool/image/lifecycle/logs/timings remain in receipts. No original
bytes, shared indexes/browser/DB or Lean modules changed. Census coverage/gaps and
observation/formal limits remain explicit. No full local make check, exhaustive
upstream test or formal equivalence claim. CI remains required. Other profiles,
including actual FIPS_SHARED research builds, are not counted in these18 rows.
