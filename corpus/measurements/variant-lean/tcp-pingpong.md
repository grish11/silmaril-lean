# TCP pingpong variant structural checks

All 32 delivered variants are whole-file parsed and structurally decomposed:
client and server, x86_64 and AArch64, O0/Og/O1/O3, stripped and unstripped.
The measured `--wfail` run is `d2957817-99b9-4f09-b9be-f4107e8bb249`:
132.679 seconds wall, 3,138,380 KiB maximum child RSS, two configured workers.
The receipt binds every generated Lean module and ELF input by SHA256.

Checked variant coverage becomes 96/408: 32 TCP pingpong, 32 cJSON, 16 darkhttpd
and 16 mimalloc. No new artifact build or semantic correctness claim is made.
Canonical whole-file coverage and formal semantic statement counts are unchanged
by this tranche. ELF bytes remain ordinary Git files outside the corpus SQLite DB.
