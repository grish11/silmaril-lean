module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Mem
public import Silmaril.Elf.Link.Dyn.Sha256sum.ListingDigest

/-! # GNU `sha256sum`: image facts for `digest_file`

The code of `digest_file` (`0x6a40`, with `sha256_stream` inlined), `fopen_safer` (`0x4e90`) and
its `fopen` wrapper (`0x4dc0`), the GOT slots they read (libc's `fopen`, `posix_fadvise`,
`malloc`, `free`, `__fread_unlocked_chk`; libcrypto's `SHA256_Init/Update/Final` at `kb`), and
the mode string `"r"` (`0x70bd`).
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

structure ShaMemD (b lb kb : Word) (mem : Memory) : Prop where
  fopenR : Loaded mem (b + 0x4dc0#64) fopenRText
  fopenSafer : Loaded mem (b + 0x4e90#64) fopenSaferText
  digestFile : Loaded mem (b + 0x6a40#64) digestFileText
  rstr : mem.readBytes (b + 0x70bd#64).toNat 2 = some [0x72#8, 0#8]
  fopen : loadN mem (b + 0x9ed0#64) 8 = some (lb + 0x85f40#64)
  fadvise : loadN mem (b + 0x9e58#64) 8 = some (lb + 0x11b7f0#64)
  malloc : loadN mem (b + 0x9ee8#64) 8 = some (lb + 0xad750#64)
  free : loadN mem (b + 0x9ed8#64) 8 = some (lb + 0xade30#64)
  freadChk : loadN mem (b + 0x9f60#64) 8 = some (lb + 0x137130#64)
  shaInit : loadN mem (b + 0x9e48#64) 8 = some (kb + 0x33d3c0#64)
  shaUpdate : loadN mem (b + 0x9f50#64) 8 = some (kb + 0x33d410#64)
  shaFinal : loadN mem (b + 0x9f90#64) 8 = some (kb + 0x33d630#64)

def shaRoPh : Elf.Phdr := ⟨1, 4, 0x7000, 0x7000, 0x1840, 0x1840⟩

theorem shaD_plain :
    plainOk shaFile shaTextPh shaSlots 0x4dc0 fopenRText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x4e90 fopenSaferText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x6a40 digestFileText = true ∧
    plainOk shaFile shaRoPh shaSlots 0x70bd [0x72#8, 0#8] = true := by decide +kernel

theorem shaD_slotsOk : slotOk shaSlots 0x9ed0 (.addr 2 0x85f40) = true ∧
    slotOk shaSlots 0x9e58 (.addr 2 0x11b7f0) = true ∧ slotOk shaSlots 0x9ee8 (.addr 2 0xad750) = true ∧
    slotOk shaSlots 0x9ed8 (.addr 2 0xade30) = true ∧ slotOk shaSlots 0x9f60 (.addr 2 0x137130) = true ∧
    slotOk shaSlots 0x9e48 (.addr 1 0x33d3c0) = true ∧ slotOk shaSlots 0x9f50 (.addr 1 0x33d410) = true ∧
    slotOk shaSlots 0x9f90 (.addr 1 0x33d630) = true := by decide +kernel

theorem shaD_lens : fopenRText.length = 0xc ∧ fopenSaferText.length = 0xb0 ∧
    digestFileText.length = 0x2f0 := by decide +kernel

theorem shaD_listing_ok : listingOk fopenRText fopenRListing = true ∧
    listingOk fopenSaferText fopenSaferListing = true ∧
    listingOk digestFileText digestFileListing = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem shaMemD_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMemD b lb kb mem := by
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
  obtain ⟨p1, p2, p3, p4⟩ := shaD_plain
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := shaD_slotsOk
  obtain ⟨l1, l2, l3⟩ := shaD_lens
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact himg.readPlain (l := fopenRText) hT htext rfl (by decide) (by rw [l1]; decide)
      (by rw [l1]; decide) (acc := .execute) rfl p1
  · exact himg.readPlain (l := fopenSaferText) hT htext rfl (by decide) (by rw [l2]; decide)
      (by rw [l2]; decide) (acc := .execute) rfl p2
  · exact himg.readPlain (l := digestFileText) hT htext rfl (by decide) (by rw [l3]; decide)
      (by rw [l3]; decide) (acc := .execute) rfl p3
  · exact himg.readPlain (l := [0x72#8, 0#8]) hT hro rfl (by decide) (by decide) (by decide)
      (acc := .read) rfl p4
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s6 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s7 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s8 (by rfl)

theorem ShaMemD.keep {b lb kb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemD b lb kb m) (h : Keeps (ShaImg b) m m') : ShaMemD b lb kb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  obtain ⟨l1, l2, l3⟩ := shaD_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa188 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨by omega, by omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h3
  · unfold Memory.readBytes at h4 ⊢
    rw [skeeps_range (off := 0x70bd) hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h4
  · exact (hl (off := 0x9ed0) (by decide)).trans h5
  · exact (hl (off := 0x9e58) (by decide)).trans h6
  · exact (hl (off := 0x9ee8) (by decide)).trans h7
  · exact (hl (off := 0x9ed8) (by decide)).trans h8
  · exact (hl (off := 0x9f60) (by decide)).trans h9
  · exact (hl (off := 0x9e48) (by decide)).trans h10
  · exact (hl (off := 0x9f50) (by decide)).trans h11
  · exact (hl (off := 0x9f90) (by decide)).trans h12

end Silmaril.Elf.Link.Dyn.Sha256sum
