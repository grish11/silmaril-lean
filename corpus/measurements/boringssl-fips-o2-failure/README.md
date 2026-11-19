# Pinned GCC14 FIPS_SHARED O2 build failure

The actual native x86_64 FIPS_SHARED O2 build of pinned BoringSSL ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6
failed while executing upstream's GNU ld-r command with crypto/fipsmodule/fips_shared.lds.
GCC14.2's bcm.cc.o code referenced data.rel.ro.local sections discarded by that
upstream script's explicit guard. See [actual build log](build-a.log.gz).
[Measured failed command](failed-build-measurement.json) preserves exact source/recipe identity, command, exit code and actual CPU/wall/RSS accounting. No ELF/BCM O2 artifact, successful repeat, strip or runtime result is claimed.

The previous five profiles (no-asm O0/O2, asm O0/O2, FIPS_SHARED O0) passed. The
[unaltered pool lifecycle](pool-lifecycle.json) records global failure and successful
removal of both workers. Its last profile remains status=running because the prior
runner only finalized successful profiles; the pool failure/stopped/removal fields
are authoritative. The sequential queue stopped without retry or overlapping pools.
No upstream linker/integrity guard, compiler identity or isolation setting changed.
This is a compiler/configuration build limitation, not evidence of FIPS validation,
certification, source semantics or equivalence. Remaining targets/profiles were
not run in this failed pool.
