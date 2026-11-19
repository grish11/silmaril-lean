module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesErr
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuoteX
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesSpec

/-! # GNU `sha256sum`: the frame of `quotef`'s run

`QF E W b s m`: the memory `m`, met somewhere inside `quotef` entered at `s`, is related to the
entry memory as `QExit.ret` (`LibRetW E W (QW b s) s t`) needs it at the end: the caller's data
outside `QW` (`slot0` and the page below the caller's stack pointer) is kept, so is every mapped,
non-private byte outside `QW`, private memory grew only into unmapped memory, the permissions of
the client's mapped memory and of the stack are those of `s`, `errno`'s bytes are kept, and every
stream is as it was.

* `QF.refl`; `QF.local`: a run of program stores into `QW` that keeps `errno` (and no mapping);
* `QF.call`: a library call with `LibRet … (fun _ => False)` that keeps the streams and `errno`;
* `QF.final`: `QF` and a System V return give `LibRetW E W (QW b s) s t`;
* `QF.keepK`: the program's kept memory outside `slot0` is kept (so `ShaRO`, `QSlots`, the name
  and the stack guard are);
* `storeMem_same`: storing the bytes a cell already holds keeps everything (`quotearg_n_options`
  writes `errno` back).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

/-- **The frame relation of `quotef`'s run** (entered at `s`, memory now `m`). -/
structure QF (E : Env) (W : World) (b : Word) (s : PState) (m : Memory) : Prop where
  keepC : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ QW b s a) s.m.memory m
  keepL : Keeps (fun a => ¬ E.S.priv s.m.memory a ∧ ¬ QW b s a ∧ s.m.memory.permits .read a = true)
    s.m.memory m
  priv : ∀ a, E.S.priv m a → E.S.priv s.m.memory a ∨ s.m.memory.permits .read a = false
  perm : ∀ a, ¬ E.S.priv s.m.memory a → s.m.memory.permits .read a = true →
    ∀ acc, m.permits acc a = s.m.memory.permits acc a
  stack : ∀ a, (s.m.core.read .rsp).toNat - 0x100000 ≤ a → a < (s.m.core.read .rsp).toNat + 0x100000 →
    ∀ acc, m.permits acc a = s.m.memory.permits acc a
  errno : Keeps (ErrnoR E) s.m.memory m
  streams : ∀ f st, E.S.file s.m.memory f st → E.S.file m f st

theorem QF.refl (E : Env) (W : World) (b : Word) (s : PState) : QF E W b s s.m.memory :=
  ⟨Keeps.refl _ _, Keeps.refl _ _, fun _ h => Or.inl h, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    Keeps.refl _ _, fun _ _ h => h⟩

theorem keeps_comb {P : Nat → Prop} {m1 m2 m3 : Memory} {a : Nat} (h1 : Keeps P m1 m2)
    (h2 : ∀ a, P a → m3.bytes.get? a = m2.bytes.get? a ∧ ∀ acc, m3.permits acc a = m2.permits acc a)
    (ha : P a) : m3.bytes.get? a = m1.bytes.get? a ∧ ∀ acc, m3.permits acc a = m1.permits acc a :=
  ⟨(h2 a ha).1.trans (h1 a ha).1, fun acc => ((h2 a ha).2 acc).trans ((h1 a ha).2 acc)⟩

theorem permits_regions {m m' : Memory} (h : m'.regions = m.regions) (acc : Access) (a : Nat) :
    m'.permits acc a = m.permits acc a := by
  simp only [Memory.permits, h]

/-- Private memory is never in `QW` (it lies below the stack, and `slot0` is the client's). -/
theorem QF.priv_qw {E : Env} {W : World} {b : Word} {s : PState} {m : Memory} (hF : QF E W b s m)
    (hs0 : ∀ a, Slot0 b a → ¬ E.S.priv s.m.memory a ∧ s.m.memory.permits .read a = true)
    (hlo : E.S.lo + 2048 ≤ (s.m.core.read .rsp).toNat) : ∀ a, E.S.priv m a → ¬ QW b s a := by
  intro a hp hq
  rcases hq with hs | ⟨h1, h2⟩
  · rcases hF.priv a hp with h | h
    · exact (hs0 a hs).1 h
    · rw [(hs0 a hs).2] at h; cases h
  · have := E.S.priv_lo _ _ hp; omega

/-- **Program stores into `QW`** (keeping `errno` and the mapping). -/
theorem QF.local {E : Env} {W : World} {b : Word} {s : PState} {m m' : Memory} (hF : QF E W b s m)
    (hs0 : ∀ a, Slot0 b a → ¬ E.S.priv s.m.memory a ∧ s.m.memory.permits .read a = true)
    (hlo : E.S.lo + 2048 ≤ (s.m.core.read .rsp).toNat)
    (hk : Keeps (fun a => ¬ QW b s a) m m') (he : Keeps (ErrnoR E) m m') (hreg : m'.regions = m.regions) :
    QF E W b s m' := by
  have privm := hF.priv_qw hs0 hlo
  have hpk : E.S.priv m' = E.S.priv m := E.S.priv_keep _ _ (hk.mono fun a ha => privm a ha)
  refine ⟨hF.keepC.trans (hk.mono fun a ha => ha.2), hF.keepL.trans (hk.mono fun a ha => ha.2.1),
    fun a hp => hF.priv a (by rw [hpk] at hp; exact hp), fun a h1 h2 acc => ?_, fun a h1 h2 acc => ?_,
    hF.errno.trans he, fun f st h => ?_⟩
  · rw [permits_regions hreg]; exact hF.perm a h1 h2 acc
  · rw [permits_regions hreg]; exact hF.stack a h1 h2 acc
  · have h1 := hF.streams f st h
    exact (E.S.local_ m m' f st (hk.mono fun a ha => privm a (E.S.foot_priv _ _ _ _ h1 ha)) h1).1

set_option maxRecDepth 100000 in
/-- **A library call** (`fp` empty) inside `quotef`'s run. -/
theorem QF.call {E : Env} {W : World} {b : Word} {s v w : PState} (hF : QF E W b s v.m.memory)
    (hsp1 : (v.m.core.read .rsp).toNat ≤ (s.m.core.read .rsp).toNat)
    (hsp2 : (s.m.core.read .rsp).toNat ≤ (v.m.core.read .rsp).toNat + 0x100000)
    (hL : LibRet E W (fun _ => False) v w) (hO : OthersKept E v w [])
    (he : Keeps (ErrnoR E) v.m.memory w.m.memory) : QF E W b s w.m.memory := by
  obtain ⟨⟨-, hRk⟩, -, hSP, hLk, hLp, hLperm, -⟩ := hL
  have np : ∀ a, ¬ E.S.priv s.m.memory a → s.m.memory.permits .read a = true → ¬ E.S.priv v.m.memory a :=
    fun a h1 h2 hp => (hF.priv a hp).elim h1 (fun h => by rw [h2] at h; cases h)
  have rd : ∀ a, ¬ E.S.priv s.m.memory a → s.m.memory.permits .read a = true →
      v.m.memory.permits .read a = true := fun a h1 h2 => (hF.perm a h1 h2 .read).trans h2
  refine ⟨hF.keepC.trans (hRk.mono fun a ha => ⟨ha.1.elim Or.inl (fun h => Or.inr (by omega)), id⟩),
    fun a ha => keeps_comb hF.keepL (fun a ha => hLk a ⟨np a ha.1 ha.2.2, id, rd a ha.1 ha.2.2⟩) ha,
    fun a hp => ?_, fun a h1 h2 acc => ?_, fun a h1 h2 acc => ?_, hF.errno.trans he,
    fun f st h => hO f st (by simp) (hF.streams f st h)⟩
  · rcases hLp a hp with h | h
    · exact hF.priv a h
    · by_cases hps : E.S.priv s.m.memory a
      · exact Or.inl hps
      · by_cases hr : s.m.memory.permits .read a = true
        · rw [rd a hps hr] at h; cases h
        · exact Or.inr (by simpa using hr)
  · rw [hLperm a (np a h1 h2) (rd a h1 h2) acc, hF.perm a h1 h2 acc]
  · by_cases ha : a < (v.m.core.read .rsp).toNat + 0x100000
    · have hlo : (v.m.core.read .rsp).toNat - 0x100000 ≤ a := (Nat.sub_le_sub_right hsp1 _).trans h1
      exact (hSP a hlo ha acc).trans (hF.stack a h1 h2 acc)
    · have hge : (v.m.core.read .rsp).toNat ≤ a := by omega
      exact ((hRk a ⟨Or.inr hge, id⟩).2 acc).trans (hF.stack a h1 h2 acc)

/-- **The end of `quotef`'s run**: the frame relation and a System V return are `LibRet`. -/
theorem QF.final {E : Env} {W : World} {b : Word} {s t : PState} (hF : QF E W b s t.m.memory)
    (habi : AbiReturn s.m.core s.m.memory t.m.core) (hfs : t.m.core.fsBase = s.m.core.fsBase) :
    LibRetW E W (QW b s) s t :=
  ⟨⟨habi, hF.keepC⟩, hfs, fun a h1 h2 acc => hF.stack a h1 h2 acc, hF.keepL, hF.priv, hF.perm⟩

/-- The program's kept memory outside `slot0` is kept. -/
theorem QF.keepK {E : Env} {W : World} {b : Word} {s : PState} {m : Memory} (hF : QF E W b s m)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 2048) :
    Keeps (fun a => W.Kept a ∧ ¬ Slot0 b a) s.m.memory m :=
  hF.keepC.mono fun a ha => ⟨Or.inl ha.1, fun hq => hq.elim ha.2 fun h =>
    (hroom.2.2 a h.1 (by omega)).2.2 ha.1⟩

/-- The streams `OthersKept` asks for. -/
theorem QF.others {E : Env} {W : World} {b : Word} {s t : PState} (hF : QF E W b s t.m.memory) :
    OthersKept E s t [] := fun f st _ h => hF.streams f st h

/-- **Storing the bytes a cell already holds** changes nothing. -/
theorem storeMem_same {m : Memory} {a v : Word} {k : Nat}
    (h : m.readBytes a.toNat k = some (Silmaril.X86.Ext.leBytes v k)) :
    Keeps (fun _ => True) m (storeMem m a k v) := by
  intro x _
  refine ⟨?_, fun _ => rfl⟩
  simp only [storeMem]
  by_cases hx : a.toNat ≤ x ∧ x < a.toNat + k
  · have hl : x - a.toNat < (Silmaril.X86.Ext.leBytes v k).length := by simp; omega
    have h1 := Memory.install_get m.bytes a.toNat (Silmaril.X86.Ext.leBytes v k) (x - a.toNat) hl
    have h2 := Memory.readWith_get h (x - a.toNat) hl
    rw [show a.toNat + (x - a.toNat) = x by omega] at h1 h2
    rw [h1, h2]
  · exact Memory.install_outside m.bytes _ _ x (by simp; omega)

theorem QF.room {E : Env} {W : World} {b : Word} {s : PState} {m : Memory} (hF : QF E W b s m)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 2048) : Room W m (s.m.core.read .rsp) 2048 :=
  hroom.keeps fun a h1 h2 acc => hF.stack a ((Nat.sub_le_sub_left (by decide) _).trans h1) (by omega) acc

/-! ## The stack of the run, and the loop invariant

`R` is the stack pointer at `quotef`'s entry. The three frames (offsets below `R`):

* `quotef`: saved `rbp` (`8`), the guard copy (`0x10`), the options (`0x48`–`0x10`), the return
  address `0x6994` (`0x50`);
* `quotearg_n_options` (`0x6720`, `rbp = R-0x58`): saved `rbp`, `r15`, `r14`, `r13`, `r12`, `rbx`
  (`0x58`–`0x80`), the saved `errno` (`0x94`, four bytes), the two stack arguments (`0xc0`, `0xc8`:
  the options' quote strings, both `NULL`), the return address `0x6859` (`0xd0`);
* `quotearg_buffer_restyled` (`0x4f50`, `rbp = R-0xd8`): saved `rbp`, `r15` (`&slotvec0`), `r14`
  (256), `r13` (`slot0`), `r12` (the options), `rbx` (`&errno`) (`0xd8`–`0x100`), the guard copy
  (`0x110`), `len` (`0x130`), the style `2` (`0x134`), `backslash_escapes` (`0x135`),
  `encountered_single_quote` (`0x136`), `elide_outer_quotes` (`0x137`), the pending byte (`0x140`),
  the name (`0x148`), `quote_string_len = 1` (`0x150`), `quote_these_too` (`0x158`, `= R-0x40`),
  `quote_string = "'"` (`0x190`). -/

/-- The cells of the run's stack the loop does not write. -/
structure QStk (E : Env) (b : Word) (s : PState) (g ev : Word) (M : Memory) : Prop where
  f8 : loadN M (s.m.core.read .rsp - 8#64) 8 = some (s.m.core.read .rbp)
  f10 : loadN M (s.m.core.read .rsp - 0x10#64) 8 = some g
  q1 : loadN M (s.m.core.read .rsp - 0x3c#64) 4 = some 0x04000000#64
  q2 : loadN M (s.m.core.read .rsp - 0x38#64) 4 = some 0#64
  q3 : loadN M (s.m.core.read .rsp - 0x34#64) 4 = some 0#64
  f50 : loadN M (s.m.core.read .rsp - 0x50#64) 8 = some (b + 0x6994#64)
  f58 : loadN M (s.m.core.read .rsp - 0x58#64) 8 = some (s.m.core.read .rsp - 8#64)
  f60 : loadN M (s.m.core.read .rsp - 0x60#64) 8 = some (s.m.core.read .r15)
  f68 : loadN M (s.m.core.read .rsp - 0x68#64) 8 = some (s.m.core.read .r14)
  f70 : loadN M (s.m.core.read .rsp - 0x70#64) 8 = some (s.m.core.read .r13)
  f78 : loadN M (s.m.core.read .rsp - 0x78#64) 8 = some (s.m.core.read .r12)
  f80 : loadN M (s.m.core.read .rsp - 0x80#64) 8 = some (s.m.core.read .rbx)
  f94 : M.readBytes (s.m.core.read .rsp - 0x94#64).toNat 4 = some (Silmaril.X86.Ext.leBytes ev 4)
  fc0 : loadN M (s.m.core.read .rsp - 0xc0#64) 8 = some 0#64
  fc8 : loadN M (s.m.core.read .rsp - 0xc8#64) 8 = some 0#64
  fd0 : loadN M (s.m.core.read .rsp - 0xd0#64) 8 = some (b + 0x6859#64)
  fd8 : loadN M (s.m.core.read .rsp - 0xd8#64) 8 = some (s.m.core.read .rsp - 0x58#64)
  fe0 : loadN M (s.m.core.read .rsp - 0xe0#64) 8 = some (b + 0xa020#64)
  fe8 : loadN M (s.m.core.read .rsp - 0xe8#64) 8 = some 256#64
  ff0 : loadN M (s.m.core.read .rsp - 0xf0#64) 8 = some (b + 0xa060#64)
  ff8 : loadN M (s.m.core.read .rsp - 0xf8#64) 8 = some (s.m.core.read .rsp - 0x48#64)
  f100 : loadN M (s.m.core.read .rsp - 0x100#64) 8 = some E.errnoA
  f110 : loadN M (s.m.core.read .rsp - 0x110#64) 8 = some g
  f134 : loadN M (s.m.core.read .rsp - 0x134#64) 4 = some 2#64
  f135 : loadN M (s.m.core.read .rsp - 0x135#64) 1 = some 1#64
  f136 : loadN M (s.m.core.read .rsp - 0x136#64) 1 = some 0#64
  f137 : loadN M (s.m.core.read .rsp - 0x137#64) 1 = some 1#64
  f148 : loadN M (s.m.core.read .rsp - 0x148#64) 8 = some (s.m.core.read .rdi)
  f150 : loadN M (s.m.core.read .rsp - 0x150#64) 8 = some 1#64
  f158 : loadN M (s.m.core.read .rsp - 0x158#64) 8 = some (s.m.core.read .rsp - 0x40#64)
  f190 : loadN M (s.m.core.read .rsp - 0x190#64) 8 = some (b + 0x70d7#64)

/-- **The loop invariant at `0x50c0`** after `i` bytes of the name: `slot0[0..i)` holds them,
`len = i`. `ev` is `errno`'s value at entry (saved at `R-0x94`), `g` the stack guard. -/
structure QLoop (E : Env) (W : World) (b : Word) (s : PState) (p : List Byte) (g ev : Word) (i : Nat)
    (w : PState) : Prop where
  rip : w.m.core.rip = b + 0x50c0#64
  rsp : w.m.core.read .rsp = s.m.core.read .rsp - 0x1c8#64
  rbp : w.m.core.read .rbp = s.m.core.read .rsp - 0xd8#64
  rbx : w.m.core.read .rbx = BitVec.ofNat 64 i
  r9 : w.m.core.read .r9 = b + 0xa060#64
  r11 : w.m.core.read .r11 = 256#64
  r14 : w.m.core.read .r14 = 0xffffffffffffffff#64
  fs : w.m.core.fsBase = s.m.core.fsBase
  gh : w.g = s.g
  stk : QStk E b s g ev w.m.memory
  len : loadN w.m.memory (s.m.core.read .rsp - 0x130#64) 8 = some (BitVec.ofNat 64 i)
  pend : ∃ x, loadN w.m.memory (s.m.core.read .rsp - 0x140#64) 1 = some x
  pre : w.m.memory.readBytes (b + 0xa060#64).toNat i = some (p.take i)
  F : QF E W b s w.m.memory
  le : i ≤ p.length
  /-- the guard at entry -/
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  /-- `errno` at entry, and the cell's permissions (`ErrnoCell`, from `__errno_location`) -/
  ebytes : s.m.memory.readBytes E.errnoA.toNat 4 = some (Silmaril.X86.Ext.leBytes ev 4)
  ecell : ErrnoCell E W s.m.memory

/-! ## The three pieces of `Task.quotefTail` -/

/-- **From `0x6720` to the loop head** (open): `quotearg_n_options`'s prologue and
`__errno_location`, the call of `quotearg_buffer_restyled`, its prologue,
`__ctype_get_mb_cur_max`, the style jump table (`0x7f48`, entry 3 → `0x588a`), `0x5860`, `0x50b8`. -/
def Task.quotePro (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (Q : PState → Prop) (s u : PState) (p : List Byte), QEntry E W b lb s p → QPlain p → QAfter b s u →
    (∀ w g ev, QLoop E W b s p g ev 0 w → MustQ W Q w) → MustQ W Q u

/-- **One iteration of the loop on a safe byte** (open). -/
def Task.quoteIter (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (s w : PState) (p : List Byte) (g ev : Word) (i : Nat), QEntry E W b lb s p → QPlain p →
    QLoop E W b s p g ev i w → i < p.length → MustQ W (QLoop E W b s p g ev (i + 1)) w

/-- **The NUL ends the loop; the returns** (open): `0x5f99` → `0x6220` → `0x6614` (the
terminator) → the epilogue, `0x6859` (`len < 256`), `errno` restored, `quotef`'s epilogue. -/
def Task.quoteExit (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (Q : PState → Prop) (s w : PState) (p : List Byte) (g ev : Word), QEntry E W b lb s p → QPlain p →
    QLoop E W b s p g ev p.length w → (∀ t, QExit E W b s t p → MustQ W Q t) → MustQ W Q w

/-- **`Task.quotefTail` from its three pieces** (the loop by `must_loop`, measure
`p.length - rbx`). -/
theorem task_quotefTail_of {E : Env} {W : World} {b lb : Word} (hP : Task.quotePro E W b lb)
    (hI : Task.quoteIter E W b lb) (hX : Task.quoteExit E W b lb) : Task.quotefTail E W b lb := by
  intro Q s u p hE hpl hA k
  refine hP Q s u p hE hpl hA fun w g ev hL => ?_
  have hfit : p.length < 256 := by
    have := hE.fits
    rwa [FilesSpec.quotef_plain _ (by simpa [toSpec] using hpl.1) hpl.2, toSpec, List.length_map] at this
  refine must_loop (fun v => p.length - (v.m.core.read .rbx).toNat)
    (fun v => ∃ i, QLoop E W b s p g ev i v) ?_ w ⟨0, hL⟩
  rintro v ⟨i, hv⟩
  by_cases hi : i < p.length
  · refine (hI s v p g ev i hE hpl hv hi).mono (fun _ h => h) fun t ht => Or.inr ⟨⟨i + 1, ht⟩, ?_⟩
    rw [ht.rbx, hv.rbx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · have he : i = p.length := by have := hv.le; omega
    subst he
    exact (hX Q s v p g ev hE hpl hv k).mono (fun _ h => h) fun _ h => Or.inl h

end Silmaril.Elf.Link.Dyn.Sha256sum
