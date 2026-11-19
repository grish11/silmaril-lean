module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemDigest
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Close
public import Silmaril.Elf.Link.Dyn.Streams.Errors
public import Silmaril.Apps.Sha256sum.Quote

/-! # GNU `sha256sum`: the statement of gnulib's `quotef`

`digest_file` names a file it cannot open with `error (0, errno, "%s", quotef (name))`.
`quotef` (`0x6950`) is gnulib's `quotearg_n_style_colon (0, shell_escape_quoting_style, name)`:
it builds the quoting options on its stack and calls `quotearg_n_options` (`0x6720`, with `n = 0`
and `argsize = SIZE_MAX` propagated), which saves `errno`, quotes the name into slot 0 with
`quotearg_buffer_restyled` (`0x4f50`, about 1350 instructions) and restores `errno`.

`Task.quotef` states what `quotef` does when the quoted name fits the static 256-byte buffer
`slot0` (`0xa060`) that slot 0 starts with (`QSlots`: gnulib's initial `nslots = 1`,
`slotvec = &slotvec0`, `slotvec0 = {256, slot0}`): it returns `slot0` holding the specification's
`quotef` of the name as a C string, writes nothing of the caller's but `slot0` (and its own stack
below the caller's), keeps `errno`, the streams and the slot table. Longer results take gnulib's
`free`/`xcharalloc` path (not stated).

The statement assumes the code and the read-only data of the pinned executable (`ShaRO`: the
memory agrees with a loaded image on `[0x2000, 0xa000)`, which holds `.text`, `.rodata` and the
GOT) and contracts for the three functions the plain-name path calls: `__errno_location`,
`__ctype_get_mb_cur_max` and `memcmp` (`quotearg_buffer_restyled` compares each byte with the
quote string `'`). Names with bytes outside gnulib's always-safe set may reach `__ctype_b_loc`
(`isprint`) and, for multibyte checks, `mbrtoc32`/`iswprint`/`mbsinit`; a proof covering them
needs their contracts too.

**Status.** `quotef` builds its options with SSE moves (`movdqa`/`movups`/`pxor` at
`0x6958`–`0x698b`), which the process machine's `Open9` does not decode: the process stops at
`0x6958` (`FilesQuoteStop.sha_quotef_stops`), so `Task.quotef` is not provable on the current
machine. The rest of the path (`quotearg_n_options`, `quotearg_buffer_restyled`) is
`Open9`-decodable; on a plain name it calls only `__errno_location` and
`__ctype_get_mb_cur_max` (no `memcmp`: gnulib switches to `shell_always_quoting_style` before
the loop, which skips the right-quote check).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

/-- The static buffer `slot0` (`.bss` `0xa060`, 256 bytes). -/
def Slot0 (b : Word) (a : Nat) : Prop := b.toNat + 0xa060 ≤ a ∧ a < b.toNat + 0xa160

/-- gnulib `quotearg`'s slot table as loaded: one slot, `slotvec = &slotvec0`,
`slotvec0 = {256, slot0}`. -/
structure QSlots (b : Word) (m : Memory) : Prop where
  nslots : loadN m (b + 0xa010#64) 4 = some 1#64
  size : loadN m (b + 0xa020#64) 8 = some 256#64
  val : loadN m (b + 0xa028#64) 8 = some (b + 0xa060#64)
  vec : loadN m (b + 0xa030#64) 8 = some (b + 0xa020#64)

/-- The executable's code, read-only data and GOT (`[0x2000, 0xa000)`) are as the loader left
them, for the pinned `sha256sum` and libraries agreeing with the recorded chunks. -/
def ShaRO (b lb : Word) (m : Memory) : Prop :=
  ∃ (Fk Fc Fl : Blob) (kb ldb res : Word) (ifn : Word → Option Word) (m0 : Memory),
    ChunksOf Fk cryptoChunks ∧ ChunksOf Fc libcChunks ∧ ChunksOf Fl ldChunks ∧
    ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res m0 ∧
    Keeps (fun a => b.toNat + 0x2000 ≤ a ∧ a < b.toNat + 0xa000) m0 m

/-- The memory `quotef` may write besides the library's: `slot0` and the stack below the
caller's (a page). -/
def QW (b : Word) (s : PState) (a : Nat) : Prop :=
  Slot0 b a ∨ ((s.m.core.read .rsp).toNat - 2048 ≤ a ∧ a < (s.m.core.read .rsp).toNat)

/-- The imports `quotef` calls on a plain name, at the addresses the GOT holds. -/
structure QImps (E : Env) (W : World) (b lb : Word) (m : Memory) : Prop where
  lz : W.lazy = none
  img : W.InImage = ShaImg b
  hb : b.toNat + 0xa188 < 2 ^ 64
  errno : ImpOk W (lb + 0x2a6e0#64) (nm "__errno_location") (errnoLocStep E W)
  mbcur : ImpOk W (lb + 0x39480#64) (nm "__ctype_get_mb_cur_max") (mbCurMaxStep E W)
  memcmp : ∃ a, loadN m (b + 0x9e18#64) 8 = some a ∧ ImpOk W a (nm "memcmp") (memcmpStep E W)

/-- **The frame of a library-like call without the resource clauses**: `LibRet` less its last two
conjuncts (`NoMap`, `NoNewStream`), the frame `quotef`'s run provides as a whole (those two do not
compose across the calls it makes). -/
def LibRetW (E : Env) (W : World) (fp : Nat → Prop) (s t : PState) : Prop :=
  Imports.ReturnsExcept W fp s t ∧ t.m.core.fsBase = s.m.core.fsBase ∧ StackPerm s t ∧
  Keeps (fun a => ¬ E.S.priv s.m.memory a ∧ ¬ fp a ∧ s.m.memory.permits .read a = true)
    s.m.memory t.m.memory ∧
  (∀ a, E.S.priv t.m.memory a → E.S.priv s.m.memory a ∨ s.m.memory.permits .read a = false) ∧
  ∀ a, ¬ E.S.priv s.m.memory a → s.m.memory.permits .read a = true →
    ∀ acc, t.m.memory.permits acc a = s.m.memory.permits acc a

/-- `LibRet` gives `LibRetW`. -/
theorem _root_.Silmaril.Elf.Link.Dyn.Streams.LibRet.toW {E : Env} {W : World} {fp : Nat → Prop} {s t : PState} (h : LibRet E W fp s t) :
    LibRetW E W fp s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- What a call of `quotef (name)` provides. -/
structure QEntry (E : Env) (W : World) (b lb : Word) (s : PState) (p : List Byte) : Prop where
  rip : s.m.core.rip = b + 0x6950#64
  abi : AbiEntry s.m.core s.m.memory
  done : s.g.done = none
  imps : QImps E W b lb s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 2048
  lo : E.S.lo + 2048 ≤ (s.m.core.read .rsp).toNat
  ro : ShaRO b lb s.m.memory
  slots : QSlots b s.m.memory
  slot0 : ∀ a, Slot0 b a → s.m.memory.permits .read a = true ∧ s.m.memory.permits .write a = true ∧
    ¬ E.S.priv s.m.memory a
  /-- the name: a C string of the program's kept memory, outside `slot0` -/
  name : CStr s.m.memory (s.m.core.read .rdi) p
  namek : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j) ∧
    ¬ Slot0 b ((s.m.core.read .rdi).toNat + j)
  /-- the quoted name fits `slot0` -/
  fits : (Silmaril.Apps.Sha256sum.quotef (toSpec p)).length < 256
  /-- the stack guard `%fs:0x28` (both frames check it), in the program's kept memory -/
  guard : ∃ g, loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  /-- the stack guard is not in `slot0` (which `quotef` writes before the guard checks) -/
  guardq : ∀ j, j < 8 → ¬ Slot0 b ((s.m.core.fsBase + 0x28#64).toNat + j)
  /-- `errno` (thread-local storage) lies below the streams, away from the stack -/
  errnoLo : E.errnoA.toNat + 4 ≤ E.S.lo
  /-- `errno` holds a value (`quotearg_n_options` saves it) -/
  errnoRd : ∃ v, loadN s.m.memory E.errnoA 4 = some v

/-- What `quotef` guarantees on return. -/
structure QExit (E : Env) (W : World) (b : Word) (s t : PState) (p : List Byte) : Prop where
  ret : LibRetW E W (QW b s) s t
  g : t.g = s.g
  streams : OthersKept E s t []
  errno : ∀ e, ErrnoIs E s.m.memory e → ErrnoIs E t.m.memory e
  rax : t.m.core.read .rax = b + 0xa060#64
  str : CStr t.m.memory (b + 0xa060#64) (ofSpec (Silmaril.Apps.Sha256sum.quotef (toSpec p)))
  slots : QSlots b t.m.memory
  slot0 : ∀ a, Slot0 b a → t.m.memory.permits .read a = true ∧ t.m.memory.permits .write a = true ∧
    ¬ E.S.priv t.m.memory a

/-- **gnulib's `quotef` on a name whose quoted form fits `slot0`** (open). -/
def Task.quotef (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (Q : PState → Prop) (s : PState) (p : List Byte), QEntry E W b lb s p →
    (∀ t, QExit E W b s t p → MustQ W Q t) → MustQ W Q s

end Silmaril.Elf.Link.Dyn.Sha256sum
