# Assembly configuration recipe (not built)

The default remains the existing `no-asm` configuration. The runner also accepts an explicit separate `asm` identity:

```sh
corpus/toolchain/image.sh
python3 scripts/corpus/variants.py --package openssl --configuration asm --arch x86_64 --level O1 --work /work/out/openssl-asm-builds
```

This uses the same pinned OpenSSL3.5.9 archive, standard image ID/lock validation and bounded two-clean-build/repeat/strip/test/receipt pipeline. Outputs, when successfully completed, belong under `corpus/variants/openssl/3.5.9/asm/...`; they cannot overwrite `no-asm`. No outputs or run measurements are included by this recipe contribution. Docker initialization is currently blocked by the task's session-keyring quota error; the complete two-clean-build recipe has not been exercised in the pinned container and must not be called a delivered assembly-enabled corpus.

Configure enables its target-selected generated assembly by omitting `no-asm`. Collection conservatively preserves available `.pl`/`.pm` generators/libraries, Configure/configuration inputs, available pristine `.s`/`.S`, generated/modified `.s`/`.S`, configdata.pm, C/header dependencies and licence inputs. A generated assembly-provenance.json hashes these inputs, records Perl/compiler/assembler versions, and separates generator command lines present in build logs from merely available generator inputs. Full build logs remain in each completed profile's measured receipts.

This distinction matters: generated standalone assembly is not C inline assembly. Neither `asm` nor `no-asm` proves that C inline assembly or compiler builtins are absent; the preserved C inputs require separate analysis. An available assembly source is not automatically compiled/linked, and an observed tool invocation is not a Lean theorem or functional validation. The actual ELF instruction census is generated only after a successful artifact build.

No assembler, compiler or dependency version is invented here: the helper records the tools it actually executes inside the standard pinned image. Missing tools or logs fail collection. BoringSSL/BoringCrypto, additional OpenSSL versions/configurations and semantic coverage are separate outstanding work.

Source-stage validation did run inside the already-existing exact pinned image: all four real Configure profiles (both architectures × asm/no-asm) passed, and configdata.pm reports the intended assembly switch and perlasm scheme. One actual AES perlasm target per architecture was generated successfully, with exact commands and generated-byte hashes in [the source-stage checks](../measurements/openssl-configure/checks.json). These sources were not assembled or linked. Fifteen Python tests and shell syntax passed. Those checks do not replace clean compiler/reproducibility/runtime/Lean checks; the PR stays draft until actual assembly-enabled ELF builds are available.
