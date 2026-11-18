module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuotePro

/-! # GNU `sha256sum`: `quotef`'s style setup `0x588a`, `0x5860`, `0x50b8`
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

set_option linter.unusedSimpArgs false

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.X86.FnContract (AbiEntry)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x588a`–`0x58ab`: `shell_always` flags. -/
theorem qp588a {W : World} {b R : Word} {Q : PState → Prop} {c : PState}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x5860 quoteX2Text) (hrip : c.m.core.rip = b + 0x588a#64)
    (hroom : Room W c.m.memory R 2048) (hbp : c.m.core.read .rbp = R - 0xd8#64)
    (k : ∀ (c1 : State) (M' : Memory), c1.rip = b + 0x5860#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → M' = storeMem (storeMem (storeMem (storeMem (storeMem (storeMem c.m.memory
        (R - 0x140#64) 1 1#64) (R - 0x138#64) 1 0#64) (R - 0x136#64) 1 0#64) (R - 0x1a0#64) 8 0#64)
        (R - 0x135#64) 1 1#64) (R - 0x137#64) 1 1#64 → MustQ W Q ⟨⟨c1, M'⟩, c.g⟩) :
    MustQ W Q c := by
  have h4 := hroom.1
  refine must_blkX_at blk588a blk588a_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk588a, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  · refine k _ _ ?_ ?_ ?_ ?_
    · blk_simp [blk588a, hrip]; bv_omega
    · intro r; exact state_read_other (by simp)
    · exact state_fs _ _
    · exact rfl
  all_goals exact room_permR hroom (Or.inr rfl) (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x5860`–`0x5885`: `quote_string = "'"`, `len = 0`, style `2`: to `0x50b8`. -/
theorem qp5860 {W : World} {b R : Word} {Q : PState → Prop} {c : PState}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x5860 quoteX2Text) (hrip : c.m.core.rip = b + 0x5860#64)
    (hroom : Room W c.m.memory R 2048) (hbp : c.m.core.read .rbp = R - 0xd8#64)
    (k : ∀ c1 : State, c1.rip = b + 0x50b8#64 → (∀ r, r ≠ .rax → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem (storeMem (storeMem (storeMem c.m.memory
        (R - 0x150#64) 8 1#64) (R - 0x190#64) 8 (b + 0x70d7#64)) (R - 0x130#64) 8 0#64) (R - 0x134#64) 4 2#64⟩,
        c.g⟩) :
    MustQ W Q c := by
  have h4 := hroom.1
  have hq : c.m.core.rip + 0x1877#64 = b + 0x70d7#64 := by rw [hrip]; bv_omega
  refine must_blkX_at blk5860 blk5860_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5860, hbp, hq, bsub_add, bsub_sub, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow,
    Nat.reduceSub]
  · refine k _ ?_ ?_ rfl
    · blk_simp [blk5860, hrip]; bv_omega
    · intro r h1; exact state_read_other (by simp [h1])
  all_goals exact room_permR hroom (Or.inr rfl) (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x50b8`: `rbx = 0`, to the loop head. -/
theorem qp50b8 {W : World} {b : Word} {Q : PState → Prop} {c : PState}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x4f50 quoteX0Text) (hrip : c.m.core.rip = b + 0x50b8#64)
    (k : ∀ c1 : State, c1.rip = b + 0x50c0#64 → c1.read .rbx = 0#64 → (∀ r, r ≠ .rbx → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) :
    MustQ W Q c := by
  refine must_blkX_at blk50b8 blk50b8_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  blk_simp [blk50b8]
  refine k _ ?_ ?_ ?_ rfl
  · blk_simp [blk50b8, hrip, ripadd, Nat.reduceAdd]
  · blk_simp [blk50b8]; simp
  · intro r h1; exact state_read_other (by simp [h1])

end Silmaril.Elf.Link.Dyn.Sha256sum
