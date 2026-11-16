module

public import Silmaril.Elf.Link.Dyn.Loader.Defs
public import Silmaril.Elf.Link.Dyn.Pin.Bytes
public import Silmaril.Elf.Link.Dyn.Pin.Defs

/-! # GNU `sha256sum` (coreutils 9.4, Ubuntu): the pinned executable

`sha256sum` is `/usr/bin/sha256sum` from Ubuntu's `coreutils`
9.4-3ubuntu6.3 (amd64): 39336 bytes, sha256
`4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60`. PIE, `DF_BIND_NOW`,
`DT_NEEDED = [libcrypto.so.3, libc.so.6]` (Ubuntu builds coreutils with OpenSSL: the digest is
`SHA256_Init/Update/Final` of `libcrypto.so.3`, `libssl3t64` 3.0.13-0ubuntu3.16, sha256
`6866ed711dab8927e1bf82bf1cd30e828bdfc34f3cc1e83b1c9eb01ce6c37d9a`).

The file is `examples/elf/pinned/gnu-sha256sum` (GPL-3.0-or-later, GNU coreutils; notice and
corresponding source in `examples/elf/README.md` and `NOTICES/effects-examples`); `shaFile` is its
`Blob` (`blob_of%` of `Silmaril.Elf.Link.Dyn.PinBytes.sha256sum`). GENERATED (the other literals)
by an untrusted script; checked against the file by `decide +kernel` in `Sha256sum.Thms`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86.Link (Blob)

/-- `sha256sum` (39336 bytes, sha256 `4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60`). -/
def shaFile : Blob := blob_of% Silmaril.Elf.Link.Dyn.PinBytes.sha256sum

def shaInfo : Elf.DynInfo := ⟨[⟨6, 4, 0x40, 0x40, 0x2d8, 0x2d8⟩, ⟨3, 4, 0x318, 0x318, 0x1c, 0x1c⟩, ⟨1, 4, 0x0, 0x0, 0x16f8, 0x16f8⟩, ⟨1, 5, 0x2000, 0x2000, 0x4d51, 0x4d51⟩, ⟨1, 4, 0x7000, 0x7000, 0x1840, 0x1840⟩, ⟨1, 6, 0x8a10, 0x9a10, 0x628, 0x778⟩, ⟨2, 6, 0x8bc0, 0x9bc0, 0x200, 0x200⟩, ⟨4, 4, 0x338, 0x338, 0x30, 0x30⟩, ⟨4, 4, 0x368, 0x368, 0x44, 0x44⟩, ⟨1685382483, 4, 0x338, 0x338, 0x30, 0x30⟩, ⟨1685382480, 4, 0x8350, 0x8350, 0xe4, 0xe4⟩, ⟨1685382481, 6, 0x0, 0x0, 0x0, 0x0⟩, ⟨1685382482, 4, 0x8a10, 0x9a10, 0x5f0, 0x5f0⟩],
  [(0x1, 0x310), (0x1, 0x31f), (0xc, 0x2000), (0xd, 0x6d44), (0x19, 0x9a10), (0x1b, 0x8), (0x1a, 0x9a18), (0x1c, 0x8), (0x6ffffef5, 0x3b0), (0x5, 0xa68), (0x6, 0x3d8), (0xa, 0x383), (0xb, 0x18), (0x15, 0x0), (0x3, 0x9dc0), (0x2, 0x540), (0x14, 0x7), (0x17, 0x11b8), (0x7, 0xf18), (0x8, 0x2a0), (0x9, 0x18), (0x1e, 0x8), (0x6ffffffb, 0x8000001), (0x6ffffffe, 0xe78), (0x6fffffff, 0x2), (0x6ffffff0, 0xdec), (0x6ffffff9, 0x11)]⟩

def shaRela : List Elf.Rela := [⟨0x9a10, 8, 0, 15136⟩, ⟨0x9a18, 8, 0, 15072⟩, ⟨0x9a20, 8, 0, 29245⟩, ⟨0x9a40, 8, 0, 29251⟩, ⟨0x9a60, 8, 0, 29266⟩, ⟨0x9a80, 8, 0, 29272⟩, ⟨0x9aa0, 8, 0, 29279⟩, ⟨0x9ac0, 8, 0, 29284⟩, ⟨0x9ae0, 8, 0, 29291⟩, ⟨0x9b00, 8, 0, 29295⟩, ⟨0x9b20, 8, 0, 29300⟩, ⟨0x9b40, 8, 0, 29307⟩, ⟨0x9b60, 8, 0, 29312⟩, ⟨0x9b80, 8, 0, 29317⟩, ⟨0xa008, 8, 0, 40968⟩, ⟨0xa028, 8, 0, 41056⟩, ⟨0xa030, 8, 0, 40992⟩, ⟨0x9f98, 6, 5, 0⟩, ⟨0x9fa0, 6, 9, 0⟩, ⟨0x9fa8, 6, 69, 0⟩, ⟨0x9fb0, 6, 20, 0⟩, ⟨0x9fb8, 6, 22, 0⟩, ⟨0x9fc0, 6, 43, 0⟩, ⟨0x9fc8, 6, 46, 0⟩, ⟨0x9fd0, 6, 49, 0⟩, ⟨0x9fd8, 6, 58, 0⟩, ⟨0x9fe0, 6, 61, 0⟩, ⟨0x9fe8, 6, 63, 0⟩]

def shaJmpRel : List Elf.Rela := [⟨0x9dd8, 7, 1, 0⟩, ⟨0x9de0, 7, 2, 0⟩, ⟨0x9de8, 7, 4, 0⟩, ⟨0x9df0, 7, 6, 0⟩, ⟨0x9df8, 7, 7, 0⟩, ⟨0x9e00, 7, 8, 0⟩, ⟨0x9e08, 7, 10, 0⟩, ⟨0x9e10, 7, 11, 0⟩, ⟨0x9e18, 7, 12, 0⟩, ⟨0x9e20, 7, 13, 0⟩, ⟨0x9e28, 7, 14, 0⟩, ⟨0x9e30, 7, 15, 0⟩, ⟨0x9e38, 7, 16, 0⟩, ⟨0x9e40, 7, 17, 0⟩, ⟨0x9e48, 7, 18, 0⟩, ⟨0x9e50, 7, 19, 0⟩, ⟨0x9e58, 7, 21, 0⟩, ⟨0x9e60, 7, 23, 0⟩, ⟨0x9e68, 7, 24, 0⟩, ⟨0x9e70, 7, 25, 0⟩, ⟨0x9e78, 7, 27, 0⟩, ⟨0x9e80, 7, 28, 0⟩, ⟨0x9e88, 7, 29, 0⟩, ⟨0x9e90, 7, 30, 0⟩, ⟨0x9e98, 7, 31, 0⟩, ⟨0x9ea0, 7, 32, 0⟩, ⟨0x9ea8, 7, 33, 0⟩, ⟨0x9eb0, 7, 34, 0⟩, ⟨0x9eb8, 7, 35, 0⟩, ⟨0x9ec0, 7, 36, 0⟩, ⟨0x9ec8, 7, 37, 0⟩, ⟨0x9ed0, 7, 38, 0⟩, ⟨0x9ed8, 7, 39, 0⟩, ⟨0x9ee0, 7, 40, 0⟩, ⟨0x9ee8, 7, 41, 0⟩, ⟨0x9ef0, 7, 42, 0⟩, ⟨0x9ef8, 7, 44, 0⟩, ⟨0x9f00, 7, 45, 0⟩, ⟨0x9f08, 7, 47, 0⟩, ⟨0x9f10, 7, 48, 0⟩, ⟨0x9f18, 7, 50, 0⟩, ⟨0x9f20, 7, 51, 0⟩, ⟨0x9f28, 7, 52, 0⟩, ⟨0x9f30, 7, 53, 0⟩, ⟨0x9f38, 7, 54, 0⟩, ⟨0x9f40, 7, 55, 0⟩, ⟨0x9f48, 7, 56, 0⟩, ⟨0x9f50, 7, 57, 0⟩, ⟨0x9f58, 7, 59, 0⟩, ⟨0x9f60, 7, 60, 0⟩, ⟨0x9f68, 7, 62, 0⟩, ⟨0x9f70, 7, 64, 0⟩, ⟨0x9f78, 7, 65, 0⟩, ⟨0x9f80, 7, 66, 0⟩, ⟨0x9f88, 7, 67, 0⟩, ⟨0x9f90, 7, 68, 0⟩]

/-- The references of the symbol relocations, by symbol index. -/
def shaRefs : List (Nat × Elf.Ref) := [
  (5, ⟨nm "stdout", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (9, ⟨nm "program_invocation_name", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (69, ⟨nm "__cxa_finalize", true, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (20, ⟨nm "__libc_start_main", false, some ⟨nm "GLIBC_2.34", 0x69691b4, false⟩⟩),
  (22, ⟨nm "stdin", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (43, ⟨nm "stderr", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (46, ⟨nm "optind", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (49, ⟨nm "program_invocation_short_name", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (58, ⟨nm "_ITM_deregisterTMCloneTable", true, none⟩),
  (61, ⟨nm "__gmon_start__", true, none⟩),
  (63, ⟨nm "_ITM_registerTMCloneTable", true, none⟩),
  (1, ⟨nm "__printf_chk", false, some ⟨nm "GLIBC_2.3.4", 0x9691974, false⟩⟩),
  (2, ⟨nm "setvbuf", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (4, ⟨nm "__errno_location", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (6, ⟨nm "strcspn", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (7, ⟨nm "__ctype_get_mb_cur_max", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (8, ⟨nm "__ctype_tolower_loc", false, some ⟨nm "GLIBC_2.3", 0xd696913, false⟩⟩),
  (10, ⟨nm "fwrite_unlocked", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (11, ⟨nm "strlen", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (12, ⟨nm "memcmp", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (13, ⟨nm "strncmp", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (14, ⟨nm "abort", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (15, ⟨nm "fcntl", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (16, ⟨nm "fseeko", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (17, ⟨nm "mbrtoc32", false, some ⟨nm "GLIBC_2.16", 0x6969196, false⟩⟩),
  (18, ⟨nm "SHA256_Init", false, some ⟨nm "OPENSSL_3.0.0", 0x6702b20, false⟩⟩),
  (19, ⟨nm "dcgettext", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (21, ⟨nm "posix_fadvise", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (23, ⟨nm "__freading", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (24, ⟨nm "mbsinit", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (25, ⟨nm "__cxa_atexit", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (27, ⟨nm "setlocale", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (28, ⟨nm "nl_langinfo", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (29, ⟨nm "fclose", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (30, ⟨nm "bindtextdomain", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (31, ⟨nm "fileno", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (32, ⟨nm "fdopen", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (33, ⟨nm "__ctype_b_loc", false, some ⟨nm "GLIBC_2.3", 0xd696913, false⟩⟩),
  (34, ⟨nm "strrchr", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (35, ⟨nm "__stack_chk_fail", false, some ⟨nm "GLIBC_2.4", 0xd696914, false⟩⟩),
  (36, ⟨nm "dcngettext", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (37, ⟨nm "fflush", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (38, ⟨nm "fopen", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (39, ⟨nm "free", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (40, ⟨nm "exit", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (41, ⟨nm "malloc", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (42, ⟨nm "iswprint", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (44, ⟨nm "__overflow", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (45, ⟨nm "__fpending", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (47, ⟨nm "__memset_chk", false, some ⟨nm "GLIBC_2.3.4", 0x9691974, false⟩⟩),
  (48, ⟨nm "strcmp", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (50, ⟨nm "textdomain", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (51, ⟨nm "_exit", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (52, ⟨nm "realloc", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (53, ⟨nm "__fprintf_chk", false, some ⟨nm "GLIBC_2.3.4", 0x9691974, false⟩⟩),
  (54, ⟨nm "getopt_long", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (55, ⟨nm "error", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (56, ⟨nm "fputc_unlocked", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (57, ⟨nm "SHA256_Update", false, some ⟨nm "OPENSSL_3.0.0", 0x6702b20, false⟩⟩),
  (59, ⟨nm "lseek", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (60, ⟨nm "__fread_unlocked_chk", false, some ⟨nm "GLIBC_2.7", 0xd696917, false⟩⟩),
  (62, ⟨nm "clearerr_unlocked", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (64, ⟨nm "fputs_unlocked", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (65, ⟨nm "fwrite", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (66, ⟨nm "close", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (67, ⟨nm "__getdelim", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (68, ⟨nm "SHA256_Final", false, some ⟨nm "OPENSSL_3.0.0", 0x6702b20, false⟩⟩)]

end Silmaril.Elf.Link.Dyn.Sha256sum
