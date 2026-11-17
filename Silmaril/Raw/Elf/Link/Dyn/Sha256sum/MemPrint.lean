module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemClose
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemDigest
public import Silmaril.Elf.Link.Dyn.Sha256sum.ListingPrint

/-! # GNU `sha256sum`: image facts for printing a result line

The code that prints `hex(digest) ++ "  " ++ name ++ "\n"` in `main` (`0x2b8a`–`0x2c96`), the
escape test (`0x35b6`), the slow paths of the inline `putc`s (`0x3766`), `print_filename`
(`0x41a0`), the `.plt.sec` stubs, the GOT slots of `__printf_chk`, `__overflow`,
`fputs_unlocked`, `strcspn` (an ifunc: its slot holds the ifunc's choice `sc`) and `stdout`, and
the strings `"%02x"` (`0x7238`) and `"\\\n\r"` (`0x71e0`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn (addr_toNat plainOk slotOk)

structure ShaMemP (b lb sc : Word) (mem : Memory) : Prop where
  plt : Loaded mem (b + 0x23c0#64) pltSecText
  printLine : Loaded mem (b + 0x2b8a#64) printLineText
  escChk : Loaded mem (b + 0x35b6#64) escChkText
  slowPut : Loaded mem (b + 0x3766#64) slowPutText
  printFilename : Loaded mem (b + 0x41a0#64) printFilenameText
  fmtHex : mem.readBytes (b + 0x7238#64).toNat 5 = some [0x25#8, 0x30#8, 0x32#8, 0x78#8, 0#8]
  reject : mem.readBytes (b + 0x71e0#64).toNat 4 = some [0x5c#8, 0x0a#8, 0x0d#8, 0#8]
  printfChk : loadN mem (b + 0x9dd8#64) 8 = some (lb + 0x137bf0#64)
  overflow : loadN mem (b + 0x9ef8#64) 8 = some (lb + 0x95120#64)
  fputs : loadN mem (b + 0x9f70#64) 8 = some (lb + 0x91890#64)
  stdoutV : loadN mem (b + 0x9f98#64) 8 = some (lb + 0x2056a8#64)
  strcspn : loadN mem (b + 0x9df0#64) 8 = some sc

theorem shaP_plain :
    plainOk shaFile shaTextPh shaSlots 0x23c0 pltSecText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x2b8a printLineText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x35b6 escChkText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x3766 slowPutText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x41a0 printFilenameText = true ∧
    plainOk shaFile shaRoPh shaSlots 0x7238 [0x25#8, 0x30#8, 0x32#8, 0x78#8, 0#8] = true ∧
    plainOk shaFile shaRoPh shaSlots 0x71e0 [0x5c#8, 0x0a#8, 0x0d#8, 0#8] = true := by decide +kernel

theorem shaP_slotsOk : slotOk shaSlots 0x9dd8 (.addr 2 0x137bf0) = true ∧
    slotOk shaSlots 0x9ef8 (.addr 2 0x95120) = true ∧ slotOk shaSlots 0x9f70 (.addr 2 0x91890) = true ∧
    slotOk shaSlots 0x9f98 (.addr 2 0x2056a8) = true ∧ slotOk shaSlots 0x9df0 (.ifunc 2 0xb4410) = true := by
  decide +kernel

theorem shaP_lens : printLineText.length = 0x10c ∧ escChkText.length = 0x4c ∧
    slowPutText.length = 0x47 ∧ printFilenameText.length = 0x10d := by decide +kernel

theorem shaP_listing_ok : listingOk printLineText printLineListing = true ∧
    listingOk escChkText escChkListing = true ∧ listingOk slowPutText slowPutListing = true ∧
    listingOk printFilenameText printFilenameListing = true := by decide +kernel

set_option maxRecDepth 20000 in
/-- **The output path's image facts from the loader relation** (eager binding; `sc` is the
address the `strcspn` ifunc chose). -/
theorem shaMemP_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sc : Word} {ifn : Word → Option Word} {mem : Memory}
    (hsc : ifn (lb + 0xb4410#64) = some sc)
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMemP b lb sc mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have htext : shaTextPh ∈ shaInfo.phs := by decide
  have hro : shaRoPh ∈ shaInfo.phs := by decide
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := shaP_plain
  obtain ⟨s1, s2, s3, s4, s5⟩ := shaP_slotsOk
  obtain ⟨l2, l3, l4, l5⟩ := shaP_lens
  have l1 := shaC_lens.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact himg.readPlain (l := pltSecText) hT htext rfl (by decide) (by rw [l1]; decide)
      (by rw [l1]; decide) (acc := .execute) rfl p1
  · exact himg.readPlain (l := printLineText) hT htext rfl (by decide) (by rw [l2]; decide)
      (by rw [l2]; decide) (acc := .execute) rfl p2
  · exact himg.readPlain (l := escChkText) hT htext rfl (by decide) (by rw [l3]; decide)
      (by rw [l3]; decide) (acc := .execute) rfl p3
  · exact himg.readPlain (l := slowPutText) hT htext rfl (by decide) (by rw [l4]; decide)
      (by rw [l4]; decide) (acc := .execute) rfl p4
  · exact himg.readPlain (l := printFilenameText) hT htext rfl (by decide) (by rw [l5]; decide)
      (by rw [l5]; decide) (acc := .execute) rfl p5
  · exact himg.readPlain (l := [0x25#8, 0x30#8, 0x32#8, 0x78#8, 0#8]) hT hro rfl (by decide) (by decide)
      (by decide) (acc := .read) rfl p6
  · exact himg.readPlain (l := [0x5c#8, 0x0a#8, 0x0d#8, 0#8]) hT hro rfl (by decide) (by decide)
      (by decide) (acc := .read) rfl p7
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by simp [Val.word]; exact hsc)

end Silmaril.Elf.Link.Dyn.Sha256sum
