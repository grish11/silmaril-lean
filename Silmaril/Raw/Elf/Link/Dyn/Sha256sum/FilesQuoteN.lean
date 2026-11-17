module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuote

/-! # GNU `sha256sum`: `quotearg_n_options` on a plain name (statement)

`quotef` (`0x6950`) only builds its `quoting_options` on its stack (with SSE moves, which the
process machine cannot run: `FilesQuoteStop`) and calls `0x6720`, gcc's specialisation of
gnulib's `quotearg_n_options (0, name, SIZE_MAX, &options)` (`rdi = name`, `rsi = &options`).
Everything from `0x6720` on is `Open9` code. `Task.quoteN` states it on a **plain** name
(non-empty, every byte in gnulib's always-safe set `%+,-./0-9A-Z]_a-z`, so `quotef` shows it
bare: `FilesSpec.quotef_plain`) whose quoted form fits `slot0`.

The path (traced on the pinned binary; 105 instructions to the loop, 64–68 per byte, 64 after
it):

* `0x6720`: save `errno` (`__errno_location`), `nslots = 1 > 0`, call
  `quotearg_buffer_restyled (slot0, 256, name, SIZE_MAX, 3, flags | 1, &qtt, NULL, NULL)`;
* `0x4f50`: `__ctype_get_mb_cur_max`, jump table on the style (`0x7f48`) to `0x588a`:
  `backslash_escapes = elide_outer_quotes = true`, `quoting_style = shell_always`,
  `quote_string = "'"` (no `memcmp`: the right-quote test needs another style);
* the loop at `0x50c0`, one iteration per byte: bytes `> 0x3f` through the bit mask at `0x5cc0`,
  bytes `≤ 0x3f` through the jump table at `0x7f74` (both reach `0x5165`), the
  `quote_these_too` test (word `c >> 5` of `&options + 8`; only `:` is set), then `STORE (c)`
  at `0x5207`;
* the NUL ends it at `0x5f99` → `0x6220` → `0x6614` (`buffer[len] = 0`) → return `len`;
* `0x6859`: `len < 256`, restore `errno`, return `slot0`.

Block certificates for all of it: `CertQuoteX` (49 blocks over the extended lifter `Bir9X`, which
takes the `Ext8` byte forms; only quotef's SSE prologue is left out).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

/-- The `quoting_options` `quotef` builds at `o` (`quotearg_n_style_colon` with
`shell_escape_quoting_style`): style 3, flags 0, `quote_these_too` with only `:` set (word 1 bit
26, from the constant at `0x8340`), no custom quotes. -/
structure QOpts (m : Memory) (o : Word) : Prop where
  style : loadN m o 8 = some 3#64
  qtt0 : loadN m (o + 8#64) 8 = some 0x0400000000000000#64
  qtt1 : loadN m (o + 0x10#64) 8 = some 0#64
  qtt2 : loadN m (o + 0x18#64) 8 = some 0#64
  qtt3 : loadN m (o + 0x20#64) 8 = some 0#64
  left : loadN m (o + 0x28#64) 8 = some 0#64
  right : loadN m (o + 0x30#64) 8 = some 0#64

/-- What the call of `0x6720` provides: `QEntry`'s facts at `0x6720`, `rsi` the options (in the
caller's kept memory, outside `slot0`), the name plain. -/
structure QNEntry (E : Env) (W : World) (b lb : Word) (s : PState) (p : List Byte) : Prop where
  rip : s.m.core.rip = b + 0x6720#64
  abi : AbiEntry s.m.core s.m.memory
  done : s.g.done = none
  imps : QImps E W b lb s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 2048
  lo : E.S.lo + 2048 ≤ (s.m.core.read .rsp).toNat
  ro : ShaRO b lb s.m.memory
  slots : QSlots b s.m.memory
  slot0 : ∀ a, Slot0 b a → s.m.memory.permits .read a = true ∧ s.m.memory.permits .write a = true ∧
    ¬ E.S.priv s.m.memory a
  name : CStr s.m.memory (s.m.core.read .rdi) p
  namek : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j) ∧
    ¬ Slot0 b ((s.m.core.read .rdi).toNat + j)
  opts : QOpts s.m.memory (s.m.core.read .rsi)
  optsk : ∀ j, j < 0x38 → W.Kept ((s.m.core.read .rsi).toNat + j) ∧
    ¬ Slot0 b ((s.m.core.read .rsi).toNat + j)
  /-- plain: non-empty, always-safe bytes -/
  ne : p ≠ []
  safe : ∀ c ∈ toSpec p, Silmaril.Apps.Sha256sum.isSafe c = true
  fits : p.length < 256
  guard : ∃ g, loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)

/-- **`quotearg_n_options` (`0x6720`) on a plain name** (open): it returns `slot0` holding the
name (its `quotef`), with `QExit`'s guarantees. With an image machine that runs `quotef`'s SSE
prologue, `Task.quotef` on plain names is this plus 15 instructions. -/
def Task.quoteN (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (Q : PState → Prop) (s : PState) (p : List Byte), QNEntry E W b lb s p →
    (∀ t, QExit E W b s t p → MustQ W Q t) → MustQ W Q s

/-! ## The loop rule, and the sub-Tasks of `Task.quoteN`

`Task.quoteN` is `quotearg_buffer_restyled`'s plain path. Its spine is the per-byte loop at
`0x50c0`. The certificates for every block are `CertQuoteX` (over `Bir9X`, no lifter gaps). What
remains, as three sub-Tasks:

* `Task.quoteNPro`: the straight-line prologue `0x6720` → the loop head `0x50c0`
  (`quotearg_n_options`'s `nslots = 1 > 0` branch to `0x681c`, the call of
  `quotearg_buffer_restyled` at `0x6854`, its prologue, `__ctype_get_mb_cur_max`, the style
  jump table to `0x588a`/`0x5860`, loop setup), establishing `QLoopInv` at `0x50c0` with the
  index `0`.
* `Task.quoteNLoop`: one iteration of the loop body for a safe byte (`0x50c0` with the index
  `< p.length` → back to `0x50c0` with the index `+ 1`, `slot0[i] = p[i]`), by the certificates;
  chained by `must_loop` with measure `p.length - i`.
* `Task.quoteNTail`: the exit `0x5f99` → `0x6220` → `0x6614` (NUL terminator) → the epilogue
  (`0x6279`, stack-guard check) → return `len`, back in `quotearg_n_options` (`0x6859`:
  `len < 256`, restore `errno`, return `slot0`), to a `QExit` state.

`must_loop` (strong induction + `Must.bind`; cf. G's loop rule): a measure that strictly
decreases each iteration, with the invariant re-established, reaches the exit. -/
theorem must_loop {W : World} {Q : PState → Prop} (μ : PState → Nat) (I : PState → Prop)
    (h : ∀ u, I u → MustQ W (fun v => Q v ∨ (I v ∧ μ v < μ u)) u) : ∀ u, I u → MustQ W Q u := by
  have key : ∀ n u, μ u < n → I u → MustQ W Q u := by
    intro n
    induction n with
    | zero => intro u hlt; omega
    | succ n ih =>
      intro u hlt hI
      refine Silmaril.X86.RelIsa.Must.bind (h u hI) ?_
      rintro t (hQ | ⟨hIt, hμt⟩)
      · exact .done hQ
      · exact ih t (by omega) hIt
  intro u hI; exact key (μ u + 1) u (by omega) hI

/-- **The loop invariant at `0x50c0`** inside `quotearg_buffer_restyled`, after the index `i`
bytes of a plain name have been copied into `slot0`. The frame cells are gcc's layout of
`quotearg_buffer_restyled (slot0, 256, name, SIZE_MAX, 3, flags | 1, &options, NULL, NULL)`:

* `rbx = i`, `r9 = slot0 = b + 0xa060`, `r11 = 256` (the buffer size), `r14 = -1` (`argsize`),
  `rbp = sp0 - 8` (its frame);
* `[rbp-0x70] = name`, `[rbp-0x58] = i` (bytes written so far = `i`, since each byte is safe),
  `[rbp-0x5c] = 2` (`shell_always`), `[rbp-0x80] = &options`;
* the style flags `backslash_escapes = elide_outer_quotes = true` at `[rbp-0x5d]`/`[rbp-0x5f]`,
  `[rbp-0x5e] = 0`, `[rbp-0x68] = 1` (`quote_string = "'"`, first byte pending — but on a plain
  name no quote is emitted);
* `slot0[0..i) = p[0..i)` and `slot0` writable and non-private;
* the saved registers, the stack guard, `errno`, `ShaRO`, `QSlots` as at entry.

The certificates `CertQuoteX` give every block's post-state over these cells; `Task.quoteNLoop`
(whoever continues) fixes this as a `structure` and proves one iteration, chained by `must_loop`
with measure `p.length - rbx`. -/
theorem quoteNLoop_note : True := trivial

end Silmaril.Elf.Link.Dyn.Sha256sum
