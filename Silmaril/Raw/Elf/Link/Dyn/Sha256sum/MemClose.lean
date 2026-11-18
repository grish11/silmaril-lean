module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Mem
public import Silmaril.Elf.Link.Dyn.Sha256sum.ListingClose

/-! # GNU `sha256sum`: image facts for `close_stdout`

The code of `close_stdout` (`0x69b0`), gnulib's `close_stream` (`0x45c0`) and `rpl_fclose`
(`0x42b0`), the `.plt.sec` stubs, and the GOT slots they read.
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

structure ShaMemC (b lb : Word) (mem : Memory) : Prop where
  plt : Loaded mem (b + 0x23c0#64) pltSecText
  rplFclose : Loaded mem (b + 0x42b0#64) rplFcloseText
  closeStream : Loaded mem (b + 0x45c0#64) closeStreamText
  closeStdout : Loaded mem (b + 0x69b0#64) closeStdoutText
  fpending : loadN mem (b + 0x9f00#64) 8 = some (lb + 0x90880#64)
  fileno : loadN mem (b + 0x9e98#64) 8 = some (lb + 0x8ea80#64)
  freading : loadN mem (b + 0x9e60#64) 8 = some (lb + 0x90790#64)
  lseek : loadN mem (b + 0x9f58#64) 8 = some (lb + 0x11b2a0#64)
  fflush : loadN mem (b + 0x9ec8#64) 8 = some (lb + 0x858d0#64)
  fclose : loadN mem (b + 0x9e88#64) 8 = some (lb + 0x85370#64)
  stdoutV : loadN mem (b + 0x9f98#64) 8 = some (lb + 0x2056a8#64)
  stderrV : loadN mem (b + 0x9fc0#64) 8 = some (lb + 0x2056a0#64)

theorem shaC_plain :
    plainOk shaFile shaTextPh shaSlots 0x23c0 pltSecText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x42b0 rplFcloseText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x45c0 closeStreamText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x69b0 closeStdoutText = true := by decide +kernel

theorem shaC_slotsOk : slotOk shaSlots 0x9f00 (.addr 2 0x90880) = true ∧
    slotOk shaSlots 0x9e98 (.addr 2 0x8ea80) = true ∧ slotOk shaSlots 0x9e60 (.addr 2 0x90790) = true ∧
    slotOk shaSlots 0x9f58 (.addr 2 0x11b2a0) = true ∧ slotOk shaSlots 0x9ec8 (.addr 2 0x858d0) = true ∧
    slotOk shaSlots 0x9e88 (.addr 2 0x85370) = true ∧ slotOk shaSlots 0x9f98 (.addr 2 0x2056a8) = true ∧
    slotOk shaSlots 0x9fc0 (.addr 2 0x2056a0) = true := by decide +kernel

theorem shaC_lens : pltSecText.length = 0x380 ∧ rplFcloseText.length = 0x11e ∧
    closeStreamText.length = 0x66 ∧ closeStdoutText.length = 0x84 := by decide +kernel

theorem shaC_listing_ok : listingOk pltSecText pltSecListing = true ∧
    listingOk rplFcloseText rplFcloseListing = true ∧
    listingOk closeStreamText closeStreamListing = true ∧
    listingOk closeStdoutText closeStdoutListing = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem shaMemC_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMemC b lb mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have htext : shaTextPh ∈ shaInfo.phs := by decide
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  obtain ⟨p1, p2, p3, p4⟩ := shaC_plain
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := shaC_slotsOk
  obtain ⟨l1, l2, l3, l4⟩ := shaC_lens
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact himg.readPlain (l := pltSecText) hT htext rfl (by decide) (by rw [l1]; decide)
      (by rw [l1]; decide) (acc := .execute) rfl p1
  · exact himg.readPlain (l := rplFcloseText) hT htext rfl (by decide) (by rw [l2]; decide)
      (by rw [l2]; decide) (acc := .execute) rfl p2
  · exact himg.readPlain (l := closeStreamText) hT htext rfl (by decide) (by rw [l3]; decide)
      (by rw [l3]; decide) (acc := .execute) rfl p3
  · exact himg.readPlain (l := closeStdoutText) hT htext rfl (by decide) (by rw [l4]; decide)
      (by rw [l4]; decide) (acc := .execute) rfl p4
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s6 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s7 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s8 (by rfl)

theorem ShaMemC.keep {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemC b lb m) (h : Keeps (ShaImg b) m m') : ShaMemC b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  obtain ⟨l1, l2, l3, l4⟩ := shaC_lens
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
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h4
  · exact (hl (off := 0x9f00) (by decide)).trans h5
  · exact (hl (off := 0x9e98) (by decide)).trans h6
  · exact (hl (off := 0x9e60) (by decide)).trans h7
  · exact (hl (off := 0x9f58) (by decide)).trans h8
  · exact (hl (off := 0x9ec8) (by decide)).trans h9
  · exact (hl (off := 0x9e88) (by decide)).trans h10
  · exact (hl (off := 0x9f98) (by decide)).trans h11
  · exact (hl (off := 0x9fc0) (by decide)).trans h12

end Silmaril.Elf.Link.Dyn.Sha256sum
