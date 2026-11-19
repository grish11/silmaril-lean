module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Thms
public import Silmaril.Elf.Link.Dyn.Sha256sum.Listing
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccMem

/-! # GNU `sha256sum`: what the loaded image provides to its startup code -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn (addr_toNat plainOk slotOk)

/-- The image facts the startup proofs use (`lb`: `libc.so.6`'s base). -/
structure ShaMem (b lb : Word) (mem : Memory) : Prop where
  init : Loaded mem (b + 0x2000#64) shaInitText
  crt : Loaded mem (b + 0x3a40#64) shaCrtText
  fini : Loaded mem (b + 0x6d44#64) shaFiniText
  pltgot : Loaded mem (b + 0x23b0#64) shaPltGotText
  lsm : loadN mem (b + 0x9fb0#64) 8 = some (lb + 0x2a200#64)
  dereg : loadN mem (b + 0x9fd8#64) 8 = some 0#64
  gmon : loadN mem (b + 0x9fe0#64) 8 = some 0#64
  reg : loadN mem (b + 0x9fe8#64) 8 = some 0#64
  cxa : loadN mem (b + 0x9fa8#64) 8 = some (lb + 0x472c0#64)
  dso : loadN mem (b + 0xa008#64) 8 = some (b + 0xa008#64)

def shaTextPh : Elf.Phdr := ⟨1, 5, 0x2000, 0x2000, 0x4d51, 0x4d51⟩
def shaRwPh : Elf.Phdr := ⟨1, 6, 0x8a10, 0x9a10, 0x628, 0x778⟩

theorem sha_plain :
    plainOk shaFile shaTextPh shaSlots 0x2000 shaInitText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x3a40 shaCrtText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x6d44 shaFiniText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x23b0 shaPltGotText = true := by decide +kernel

theorem sha_slotsOk : slotOk shaSlots 0x9fb0 (.addr 2 0x2a200) = true ∧
    slotOk shaSlots 0x9fd8 (.abs 0) = true ∧ slotOk shaSlots 0x9fe0 (.abs 0) = true ∧
    slotOk shaSlots 0x9fe8 (.abs 0) = true ∧ slotOk shaSlots 0x9fa8 (.addr 2 0x472c0) = true ∧
    slotOk shaSlots 0xa008 (.addr 0 40968) = true := by decide +kernel

theorem sha_info_f : finfo shaFile = some shaInfo := sha_info

theorem sha_lens : shaInitText.length = 0x1b ∧ shaCrtText.length = 0xe9 ∧ shaFiniText.length = 0xd ∧
    shaPltGotText.length = 0x10 := by decide +kernel

set_option maxRecDepth 20000 in
/-- **The loader relation gives the image facts** (eager binding; `DF_BIND_NOW`). -/
theorem shaMem_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMem b lb mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have htext : shaTextPh ∈ shaInfo.phs := by decide
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  obtain ⟨p1, p2, p3, p4⟩ := sha_plain
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sha_slotsOk
  obtain ⟨l1, l2, l3, l4⟩ := sha_lens
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact himg.readPlain (l := shaInitText) hT htext rfl (by decide) (by rw [l1]; decide)
      (by rw [l1]; decide) (acc := .execute) rfl p1
  · exact himg.readPlain (l := shaCrtText) hT htext rfl (by decide) (by rw [l2]; decide)
      (by rw [l2]; decide) (acc := .execute) rfl p2
  · exact himg.readPlain (l := shaFiniText) hT htext rfl (by decide) (by rw [l3]; decide)
      (by rw [l3]; decide) (acc := .execute) rfl p3
  · exact himg.readPlain (l := shaPltGotText) hT htext rfl (by decide) (by rw [l4]; decide)
      (by rw [l4]; decide) (acc := .execute) rfl p4
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s6 (by rfl)

/-- The executable's image (extent `0xa188`). -/
def ShaImg (b : Word) (a : Nat) : Prop := b.toNat ≤ a ∧ a < b.toNat + 0xa188

theorem skeeps_range {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {P : Nat → Prop} {m m' : Memory}
    (h : Keeps P m m') {off len : Nat} (hr : off + len ≤ 0xa188)
    (hP : ∀ k < len, P (b.toNat + off + k)) {acc : Access} :
    m'.readWith acc (b + BitVec.ofNat 64 off).toNat len = m.readWith acc (b + BitVec.ofNat 64 off).toNat len := by
  rw [addr_toNat (by omega)]
  exact h.readWith hP

theorem ShaMem.keep {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMem b lb m) (h : Keeps (ShaImg b) m m') : ShaMem b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hm
  obtain ⟨l1, l2, l3, l4⟩ := sha_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa188 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨by omega, by omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨by omega, by omega⟩)]; exact h4
  · exact (hl (off := 0x9fb0) (by decide)).trans h5
  · exact (hl (off := 0x9fd8) (by decide)).trans h6
  · exact (hl (off := 0x9fe0) (by decide)).trans h7
  · exact (hl (off := 0x9fe8) (by decide)).trans h8
  · exact (hl (off := 0x9fa8) (by decide)).trans h9
  · exact (hl (off := 0xa008) (by decide)).trans h10

theorem sha_listing_ok : listingOk shaInitText shaInitListing = true ∧
    listingOk shaCrtText shaCrtListing = true ∧ listingOk shaFiniText shaFiniListing = true ∧
    listingOk shaPltGotText shaPltGotListing = true := by decide +kernel

end Silmaril.Elf.Link.Dyn.Sha256sum
