# Completed matrix continuation

This tranche adds 216 real ELF artifact rows (ordinary Git bytes): mimalloc16, jemalloc16, TinyCC16, GNU coreutils112, SQLite32 and x86_64 no-asm OpenSSL24. Catalog total462 rows /456 unique content hashes, including54 canonical O2 objects. Each completed profile retains its two clean-build runs, exact recipe/image identities, runtime tests, stripping comparisons and measured receipts beneath `corpus/variants/`.

TinyCC/coreutils upstream downloads timed out. Adjacent acquisition JSON records public mirror URLs and exact pinned hashes; no source identity changed.

The first AArch64 OpenSSL O0 container never initialized: runc returned `unable to join session keyring: unable to create session key: disk quota exceeded`. Two subsequent bounded `docker run --rm --network host ... true` probes also returned125 with the same error. No build-a run receipt or output is claimed for that failed profile. All24 AArch64 OpenSSL variants remain absent. No quotas/sysctls/keyrings/isolation settings were changed; retries stopped.

Task resources were partitioned: build roots/descendants were pinned to CPU0–5, independent Lean work to6–7. The build launcher requested8 CPU/32GiB; a watcher configured6 CPU/16GiB after creation. This sandbox did not demonstrate cgroup memory enforcement, so a configured cap must not be described as measured enforcement. Each package built serially; build commands used JOBS8 within six effective cores.

These216 additions have no Lean parse/decomposition checks and no semantic statements. The separate staged-table PR #1034 checks two earlier cJSON variants and the canonical x86_64 OpenSSL CLI; it is not part of this branch. Corpus contextual C-to-ELF and binary functional-equivalence statement counts remain zero. O2 stripped outputs, rich multi-version/configuration examples, assembly-enabled OpenSSL and BoringSSL/BoringCrypto remain undelivered.

All408 variants have artifact-specific static census reports. Census run ba414e57-40e8-42f5-860e-6bdad413c5a4 took89.539s wall /203,112KiB peak child RSS, one worker, including regeneration of earlier reports. Analysis image identity was filled from `docker inspect` of the reused pinned container (the initial exec omitted the metadata environment variable); this is provenance metadata, not a new analysis execution.

DB run872cf79e-6450-4ab4-90a6-20c87c76d6a0 passed: 5.192s wall /74,436KiB peak child RSS, one worker;462 artifact rows /456 hashes /299,597 function mapping rows. Includes no builds or Lean work; warm filesystem cache, no repeat claimed. ELF bytes remain outside SQLite. The earlier failed isolated-Python invocation receipt is retained, exit1 (local import failure), and is not a successful timing baseline. Ten corpus Python tests and diff whitespace checks passed. Full CI is pending.
