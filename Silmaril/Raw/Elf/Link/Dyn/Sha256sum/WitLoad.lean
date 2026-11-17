module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitChunks

/-! # GNU `sha256sum`: a concrete loaded process (non-vacuity, part 1)

The executable at `b0 = 0x555555554000`, `libcrypto.so.3` at `kb0`, `libc.so.6` at `lb0`, `ld.so` at
`ldb0`; library files holding exactly the pinned chunks (`Fk0`, `Fc0`, `Fl0`); every ifunc resolved
to its resolver's address (`ifn0`). The memory `memW stk` holds the loader relation's image, a
two-page stack `stk` around `sp0`, a page of libc's `.data` (`stdout`/`stderr`/`stdin` variables,
`optind`, `program_invocation_name`) and a TCB page at `fs0` (the stack guard at `fs0 + 0x28`).
`loadedW` proves the loader relation `ExeLoaded` for it, for every stack contents.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Proc.Witness

def perm (r w x : Bool) : Permissions := ⟨r, w, x⟩

/-- The executable's mappings (`PT_LOAD`s rounded to pages, as `mmap` maps them; the `RELRO` part of
the data segment read-only). The whole image range `ShaImg` is thus readable, as `MEnv.np` asks. -/
def exeRegions : List Region :=
  [⟨b0.toNat, 0x2000, perm true false false⟩, ⟨b0.toNat + 0x2000, 0x5000, perm true false true⟩,
   ⟨b0.toNat + 0x7000, 0x2000, perm true false false⟩, ⟨b0.toNat + 0x9000, 0x1000, perm true false false⟩,
   ⟨b0.toNat + 0xa000, 0x1000, perm true true false⟩]

/-- The stack (two pages around `sp0`), libc's `.data` page pair, the TCB page. -/
def stackLo : Nat := sp0.toNat - 4096
def libLo : Nat := lb0.toNat + 0x204000
def regions0 : List Region :=
  exeRegions ++ [⟨stackLo, 8192, perm true true false⟩, ⟨libLo, 0x2000, perm true true false⟩,
    ⟨fs0.toNat, 0x1000, perm true true false⟩]

def ph0 : Elf.Phdr := (loads shaInfo).getD 0 ⟨0, 0, 0, 0, 0, 0⟩
def ph1 : Elf.Phdr := (loads shaInfo).getD 1 ⟨0, 0, 0, 0, 0, 0⟩
def ph2 : Elf.Phdr := (loads shaInfo).getD 2 ⟨0, 0, 0, 0, 0, 0⟩
def ph3 : Elf.Phdr := (loads shaInfo).getD 3 ⟨0, 0, 0, 0, 0, 0⟩
theorem hL : loads shaInfo = [ph0, ph1, ph2, ph3] := by decide +kernel
theorem hsz0 : ph0.memsz = 5880 ∧ ph0.vaddr + ph0.memsz ≤ 0xa188 := by decide +kernel
theorem hsz1 : ph1.memsz = 19793 ∧ ph1.vaddr + ph1.memsz ≤ 0xa188 := by decide +kernel
theorem hsz2 : ph2.memsz = 6208 ∧ ph2.vaddr + ph2.memsz ≤ 0xa188 := by decide +kernel
theorem hsz3 : ph3.memsz = 1912 ∧ ph3.vaddr + ph3.memsz ≤ 0xa188 := by decide +kernel
theorem blk0_0 : (List.range' (2048 * 0) 2048).all (fun k => !decide (k < 5880) || byteOk shaFile shaInfo T0 b0 regions0 ph0 k) = true := by
  decide +kernel
theorem blk0_1 : (List.range' (2048 * 1) 2048).all (fun k => !decide (k < 5880) || byteOk shaFile shaInfo T0 b0 regions0 ph0 k) = true := by
  decide +kernel
theorem blk0_2 : (List.range' (2048 * 2) 2048).all (fun k => !decide (k < 5880) || byteOk shaFile shaInfo T0 b0 regions0 ph0 k) = true := by
  decide +kernel
theorem seg0 : (List.range ph0.memsz).all (byteOk shaFile shaInfo T0 b0 regions0 ph0) = true := by
  rw [hsz0.1]
  refine all_range_of_blocks (c := 2048) (m := 3) (by decide) fun j hj => ?_
  interval_cases j
  · exact blk0_0
  · exact blk0_1
  · exact blk0_2
theorem blk1_0 : (List.range' (2048 * 0) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_1 : (List.range' (2048 * 1) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_2 : (List.range' (2048 * 2) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_3 : (List.range' (2048 * 3) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_4 : (List.range' (2048 * 4) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_5 : (List.range' (2048 * 5) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_6 : (List.range' (2048 * 6) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_7 : (List.range' (2048 * 7) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_8 : (List.range' (2048 * 8) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem blk1_9 : (List.range' (2048 * 9) 2048).all (fun k => !decide (k < 19793) || byteOk shaFile shaInfo T0 b0 regions0 ph1 k) = true := by
  decide +kernel
theorem seg1 : (List.range ph1.memsz).all (byteOk shaFile shaInfo T0 b0 regions0 ph1) = true := by
  rw [hsz1.1]
  refine all_range_of_blocks (c := 2048) (m := 10) (by decide) fun j hj => ?_
  interval_cases j
  · exact blk1_0
  · exact blk1_1
  · exact blk1_2
  · exact blk1_3
  · exact blk1_4
  · exact blk1_5
  · exact blk1_6
  · exact blk1_7
  · exact blk1_8
  · exact blk1_9
theorem blk2_0 : (List.range' (2048 * 0) 2048).all (fun k => !decide (k < 6208) || byteOk shaFile shaInfo T0 b0 regions0 ph2 k) = true := by
  decide +kernel
theorem blk2_1 : (List.range' (2048 * 1) 2048).all (fun k => !decide (k < 6208) || byteOk shaFile shaInfo T0 b0 regions0 ph2 k) = true := by
  decide +kernel
theorem blk2_2 : (List.range' (2048 * 2) 2048).all (fun k => !decide (k < 6208) || byteOk shaFile shaInfo T0 b0 regions0 ph2 k) = true := by
  decide +kernel
theorem blk2_3 : (List.range' (2048 * 3) 2048).all (fun k => !decide (k < 6208) || byteOk shaFile shaInfo T0 b0 regions0 ph2 k) = true := by
  decide +kernel
theorem seg2 : (List.range ph2.memsz).all (byteOk shaFile shaInfo T0 b0 regions0 ph2) = true := by
  rw [hsz2.1]
  refine all_range_of_blocks (c := 2048) (m := 4) (by decide) fun j hj => ?_
  interval_cases j
  · exact blk2_0
  · exact blk2_1
  · exact blk2_2
  · exact blk2_3
theorem blk3_0 : (List.range' (2048 * 0) 2048).all (fun k => !decide (k < 1912) || byteOk shaFile shaInfo T0 b0 regions0 ph3 k) = true := by
  decide +kernel
theorem seg3 : (List.range ph3.memsz).all (byteOk shaFile shaInfo T0 b0 regions0 ph3) = true := by
  rw [hsz3.1]
  refine all_range_of_blocks (c := 2048) (m := 1) (by decide) fun j hj => ?_
  interval_cases j
  · exact blk3_0
theorem tableOk_true : tableOk shaFile shaInfo T0 b0 regions0 0xa188 = true := by
  unfold tableOk
  rw [hL]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hsz0.2, seg0⟩, ⟨hsz1.2, seg1⟩, ⟨hsz2.2, seg2⟩, ⟨hsz3.2, seg3⟩⟩

@[irreducible] def img0 : List Byte := imgOf shaFile shaInfo T0 0xa188

theorem img0_length : img0.length = 0xa188 := by unfold img0; exact imgOf_length _ _ _ _

/-- Bytes `l` at offset `o` of a zero page of `n` bytes. -/
def pageOf (n : Nat) (ps : List (Nat × List Byte)) : List Byte :=
  (List.range n).map fun k => (ps.findSome? fun e => if e.1 ≤ k ∧ k < e.1 + e.2.length then e.2[k - e.1]? else none).getD 0

theorem pageOf_length (n : Nat) (ps : List (Nat × List Byte)) : (pageOf n ps).length = n := by
  simp [pageOf]

/-- The stack guard. -/
def guard0 : Word := 0x2f8a6c3d00000000#64

/-- The A0-based slots of the streams (`Streams.Total.envOf`: `stdout`, `stderr`, then `stdin`). -/
def outF : Word := BitVec.ofNat 64 Silmaril.Elf.Link.Dyn.Streams.Total.A0
def errF : Word := BitVec.ofNat 64 (Silmaril.Elf.Link.Dyn.Streams.Total.A0 + Silmaril.Elf.Link.Dyn.Streams.Total.S0)
def inF : Word := BitVec.ofNat 64 (Silmaril.Elf.Link.Dyn.Streams.Total.A0 + 2 * Silmaril.Elf.Link.Dyn.Streams.Total.S0)

/-- libc's `.data` pages from `lb0 + 0x204000`: `optind = 1` (`0x248`), `stderr`, `stdout`, `stdin`
(`0x16a0`, `0x16a8`, `0x16b0`). -/
@[irreducible] def libPage : List Byte :=
  pageOf 0x2000 [(0x248, Silmaril.X86.Ext.leBytes 1#64 4), (0x16a0, Silmaril.X86.Ext.leBytes errF 8),
    (0x16a8, Silmaril.X86.Ext.leBytes outF 8), (0x16b0, Silmaril.X86.Ext.leBytes inF 8)]

/-- The TCB page: the guard at `0x28`. -/
@[irreducible] def tlsPage : List Byte := pageOf 0x1000 [(0x28, Silmaril.X86.Ext.leBytes guard0 8)]

theorem libPage_length : libPage.length = 0x2000 := by unfold libPage; exact pageOf_length _ _
theorem tlsPage_length : tlsPage.length = 0x1000 := by unfold tlsPage; exact pageOf_length _ _

/-- The process memory, for the stack contents `stk` (8192 bytes from `sp0 - 4096`). -/
def memW (stk : List Byte) : Memory :=
  ⟨regions0, Memory.install (Memory.install (Memory.install (Memory.install ∅ b0.toNat img0) stackLo stk)
    libLo libPage) fs0.toNat tlsPage⟩

set_option maxRecDepth 100000 in
theorem memW_img (stk : List Byte) {v : Nat} (hv : v < 0xa188) :
    (memW stk).bytes.get? (b0.toNat + v) = some (byteAt shaFile shaInfo T0 v) := by
  have h1 : img0[v]? = some (byteAt shaFile shaInfo T0 v) := by unfold img0; exact imgOf_get _ _ _ hv
  have hv' : v < img0.length := by rw [img0_length]; exact hv
  have hb : b0.toNat + v < 0x555555560000 := by rw [b0_toNat]; omega
  unfold memW
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inl (Nat.lt_of_lt_of_le hb (by decide)))]
  rw [Memory.install_outside _ _ _ _ (Or.inl (Nat.lt_of_lt_of_le hb (by decide)))]
  rw [Memory.install_outside _ _ _ _ (Or.inl (Nat.lt_of_lt_of_le hb (by decide)))]
  rw [Memory.install_get _ _ _ _ hv', ← List.getElem?_eq_getElem hv']
  exact h1

/-- **The loader relation** holds of `memW stk`, for every stack contents. -/
theorem loadedW (stk : List Byte) :
    ExeLoaded [shaFile, Fk0, Fc0, Fl0] [b0, kb0, lb0, ldb0] ifn0 false res0 (memW stk) :=
  ⟨shaFile, b0, shaInfo, shaSlots, T0, rfl, rfl, sha_info_f,
    ⟨fun h => absurd h (by decide), sha_slots hFk hFc hFl, hT0,
      imageOk_of_tableOk shaFile shaInfo T0 (by rw [b0_toNat]; decide) rfl (fun v hv => memW_img stk hv)
        tableOk_true⟩⟩

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
