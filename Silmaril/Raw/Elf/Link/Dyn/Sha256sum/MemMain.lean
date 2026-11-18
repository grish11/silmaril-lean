module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemPrint
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Mem
public import Silmaril.Elf.Link.Dyn.Sha256sum.ListingMain
public import Silmaril.Raw.Elf.Link.Dyn.Cert.CodeRO

/-! # GNU `sha256sum`: image facts for `main`

The code of `main` on the happy paths (`0x2750`–`0x2888`: prologue, inlined `set_program_name`,
locale set-up, `atexit (close_stdout)`, `setvbuf`, the `getopt_long` call; `0x29fd`–`0x2b8a`: the
option checks and the operand loop up to the result line; `0x2c8a`–`0x2cda`: the loop latch and the
`--zero`/`--tag` checks; `0x2cf9`–`0x2d30`: the epilogue), `atexit` (`0x6d30`), the GOT slots of
the imports `main` calls (`strrchr` is an ifunc: its slot holds the ifunc's choice `sr`), the GOT
slots of the libc variables it reads or writes (`program_invocation_name`, `optind`, `stdin`), the
string `"-"`, and the initial values of the option flags in `.data`/`.bss`.

Also: the image facts of the other helpers (`ShaMem`, `ShaMemC`, `ShaMemD`, `ShaMemP`) are kept by
any frame that keeps the image **below** the option variables `0xa160` (`main` writes `0xa168`,
`0xa178` and `0xa180`; `digest_file` writes `have_read_stdin` at `0xa160`).
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

/-- `main`'s image facts (`sr`: the address the `strrchr` ifunc chose). -/
structure ShaMemM (b lb sr : Word) (mem : Memory) : Prop where
  mainA : Loaded mem (b + 0x2750#64) mainAText
  mainC : Loaded mem (b + 0x29fd#64) mainCText
  mainD : Loaded mem (b + 0x2c8a#64) mainDText
  mainE : Loaded mem (b + 0x2cf9#64) mainEText
  atexit : Loaded mem (b + 0x6d30#64) atexitText
  dash : mem.readBytes (b + 0x716e#64).toNat 2 = some [0x2d#8, 0#8]
  delim : mem.readBytes (b + 0xa01c#64).toNat 1 = some [0x0a#8]
  flags : mem.readBytes (b + 0xa170#64).toNat 5 = some [0#8, 0#8, 0#8, 0#8, 0#8]
  setvbuf : loadN mem (b + 0x9de0#64) 8 = some (lb + 0x88630#64)
  cxaAtexit : loadN mem (b + 0x9e70#64) 8 = some (lb + 0x471f0#64)
  setlocale : loadN mem (b + 0x9e78#64) 8 = some (lb + 0x3a6b0#64)
  bindtextdomain : loadN mem (b + 0x9e90#64) 8 = some (lb + 0x3bf00#64)
  strrchr : loadN mem (b + 0x9eb0#64) 8 = some sr
  textdomain : loadN mem (b + 0x9f18#64) 8 = some (lb + 0x406f0#64)
  getopt : loadN mem (b + 0x9f38#64) 8 = some (lb + 0xf5ad0#64)
  pinV : loadN mem (b + 0x9fa0#64) 8 = some (lb + 0x205378#64)
  stdinV : loadN mem (b + 0x9fb8#64) 8 = some (lb + 0x2056b0#64)
  optindV : loadN mem (b + 0x9fc8#64) 8 = some (lb + 0x204248#64)
  /-- `main`'s code chunks are not writable (for block certificates, `Cert.must_blk`). -/
  roA : Cert.CodeRO mem (b + 0x2750#64) mainAText
  roC : Cert.CodeRO mem (b + 0x29fd#64) mainCText
  roD : Cert.CodeRO mem (b + 0x2c8a#64) mainDText

/-- The option variables of `main` and `digest_file` (`.bss`, `0xa160`–`0xa188`) are readable
and writable. -/
def ShaRw (b : Word) (mem : Memory) : Prop :=
  ∀ k, k < 0x28 → mem.permits .read (b.toNat + 0xa160 + k) = true ∧
    mem.permits .write (b.toNat + 0xa160 + k) = true

theorem shaM_plain :
    plainOk shaFile shaTextPh shaSlots 0x2750 mainAText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x29fd mainCText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x2c8a mainDText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x2cf9 mainEText = true ∧
    plainOk shaFile shaTextPh shaSlots 0x6d30 atexitText = true ∧
    plainOk shaFile shaRoPh shaSlots 0x716e [0x2d#8, 0#8] = true ∧
    plainOk shaFile shaRwPh shaSlots 0xa01c [0x0a#8] = true ∧
    plainOk shaFile shaRwPh shaSlots 0xa170 [0#8, 0#8, 0#8, 0#8, 0#8] = true := by decide +kernel

theorem shaM_slotsOk : slotOk shaSlots 0x9de0 (.addr 2 0x88630) = true ∧
    slotOk shaSlots 0x9e70 (.addr 2 0x471f0) = true ∧ slotOk shaSlots 0x9e78 (.addr 2 0x3a6b0) = true ∧
    slotOk shaSlots 0x9e90 (.addr 2 0x3bf00) = true ∧ slotOk shaSlots 0x9eb0 (.ifunc 2 0xb5210) = true ∧
    slotOk shaSlots 0x9f18 (.addr 2 0x406f0) = true ∧ slotOk shaSlots 0x9f38 (.addr 2 0xf5ad0) = true ∧
    slotOk shaSlots 0x9fa0 (.addr 2 0x205378) = true ∧ slotOk shaSlots 0x9fb8 (.addr 2 0x2056b0) = true ∧
    slotOk shaSlots 0x9fc8 (.addr 2 0x204248) = true := by
  decide +kernel

theorem shaM_lens : mainAText.length = 0x138 ∧ mainCText.length = 0x18d ∧ mainDText.length = 0x50 ∧
    mainEText.length = 0x37 ∧ atexitText.length = 0x12 := by decide +kernel

theorem shaM_listing_ok : listingOk mainAText mainAListing = true ∧
    listingOk mainCText mainCListing = true ∧ listingOk mainDText mainDListing = true ∧
    listingOk mainEText mainEListing = true ∧ listingOk atexitText atexitListing = true := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **`main`'s image facts from the loader relation** (eager binding; `sr` is the address the
`strrchr` ifunc chose). -/
theorem shaMemM_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr : Word} {ifn : Word → Option Word} {mem : Memory}
    (hsr : ifn (lb + 0xb5210#64) = some sr)
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMemM b lb sr mem := by
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
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := shaM_plain
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := shaM_slotsOk
  obtain ⟨l1, l2, l3, l4, l5⟩ := shaM_lens
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact himg.readPlain (l := mainAText) hT htext rfl (by decide) (by rw [l1]; decide)
      (by rw [l1]; decide) (acc := .execute) rfl p1
  · exact himg.readPlain (l := mainCText) hT htext rfl (by decide) (by rw [l2]; decide)
      (by rw [l2]; decide) (acc := .execute) rfl p2
  · exact himg.readPlain (l := mainDText) hT htext rfl (by decide) (by rw [l3]; decide)
      (by rw [l3]; decide) (acc := .execute) rfl p3
  · exact himg.readPlain (l := mainEText) hT htext rfl (by decide) (by rw [l4]; decide)
      (by rw [l4]; decide) (acc := .execute) rfl p4
  · exact himg.readPlain (l := atexitText) hT htext rfl (by decide) (by rw [l5]; decide)
      (by rw [l5]; decide) (acc := .execute) rfl p5
  · exact himg.readPlain (l := [0x2d#8, 0#8]) hT hro rfl (by decide) (by decide)
      (by decide) (acc := .read) rfl p6
  · exact himg.readPlain (l := [0x0a#8]) hT hrw rfl (by decide) (by decide)
      (by decide) (acc := .read) rfl p7
  · exact himg.readPlain (l := [0#8, 0#8, 0#8, 0#8, 0#8]) hT hrw rfl (by decide) (by decide)
      (by decide) (acc := .read) rfl p8
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s3 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s4 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s5 (by simp [Val.word]; exact hsr)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s6 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s7 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s8 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s9 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s10 (by rfl)
  · exact Cert.codeRO_of_imageOk himg htext rfl (by decide) (by decide) (by rw [l1]; decide)
  · exact Cert.codeRO_of_imageOk himg htext rfl (by decide) (by decide) (by rw [l2]; decide)
  · exact Cert.codeRO_of_imageOk himg htext rfl (by decide) (by decide) (by rw [l3]; decide)

/-- **The option variables are readable and writable** after loading (`.bss`, outside RELRO). -/
theorem shaRw_of_loaded {Fk Fc Fl : Blob} {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaRw b mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  have hrel : ∀ k, k < 0x28 → Silmaril.Elf.Link.Dyn.inRelro shaInfo (0xa160 + k) = false := by
    decide +kernel
  intro k hk
  obtain ⟨hwrap, hr, -, hw, -⟩ := himg shaRwPh hrw rfl (0xa160 + k) (by simp [shaRwPh]; omega)
    (by simp [shaRwPh]; omega)
  dsimp only at hwrap hr hw
  rw [addr_toNat hwrap, ← Nat.add_assoc] at hr hw
  refine ⟨by rw [hr]; simp [shaRwPh], ?_⟩
  rw [hw]
  simp [hrel k hk, shaRwPh]

/-! ## Keeping the image facts below the option variables -/

/-- The image without the option variables `main` and `digest_file` write (`0xa160`–`0xa170`
and `0xa178`–`0xa188`). -/
def ImgW (b : Word) (a : Nat) : Prop :=
  ShaImg b a ∧ (a < b.toNat + 0xa160 ∨ (b.toNat + 0xa170 ≤ a ∧ a < b.toNat + 0xa178))

theorem imgW_img {b : Word} {m m' : Memory} (h : Keeps (ShaImg b) m m') : Keeps (ImgW b) m m' :=
  h.mono fun _ ha => ha.1

theorem ShaMem.keepW {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMem b lb m) (h : Keeps (ImgW b) m m') : ShaMem b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hm
  obtain ⟨l1, l2, l3, l4⟩ := sha_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa160 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h4
  · exact (hl (off := 0x9fb0) (by decide)).trans h5
  · exact (hl (off := 0x9fd8) (by decide)).trans h6
  · exact (hl (off := 0x9fe0) (by decide)).trans h7
  · exact (hl (off := 0x9fe8) (by decide)).trans h8
  · exact (hl (off := 0x9fa8) (by decide)).trans h9
  · exact (hl (off := 0xa008) (by decide)).trans h10

theorem ShaMemC.keepW {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemC b lb m) (h : Keeps (ImgW b) m m') : ShaMemC b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  obtain ⟨l1, l2, l3, l4⟩ := shaC_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa160 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h4
  · exact (hl (off := 0x9f00) (by decide)).trans h5
  · exact (hl (off := 0x9e98) (by decide)).trans h6
  · exact (hl (off := 0x9e60) (by decide)).trans h7
  · exact (hl (off := 0x9f58) (by decide)).trans h8
  · exact (hl (off := 0x9ec8) (by decide)).trans h9
  · exact (hl (off := 0x9e88) (by decide)).trans h10
  · exact (hl (off := 0x9f98) (by decide)).trans h11
  · exact (hl (off := 0x9fc0) (by decide)).trans h12

theorem ShaMemD.keepW {b lb kb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemD b lb kb m) (h : Keeps (ImgW b) m m') : ShaMemD b lb kb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  obtain ⟨l1, l2, l3⟩ := shaD_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa160 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h3
  · unfold Memory.readBytes at h4 ⊢
    rw [skeeps_range (off := 0x70bd) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h4
  · exact (hl (off := 0x9ed0) (by decide)).trans h5
  · exact (hl (off := 0x9e58) (by decide)).trans h6
  · exact (hl (off := 0x9ee8) (by decide)).trans h7
  · exact (hl (off := 0x9ed8) (by decide)).trans h8
  · exact (hl (off := 0x9f60) (by decide)).trans h9
  · exact (hl (off := 0x9e48) (by decide)).trans h10
  · exact (hl (off := 0x9f50) (by decide)).trans h11
  · exact (hl (off := 0x9f90) (by decide)).trans h12

theorem ShaMemP.keepW {b lb sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemP b lb sc m) (h : Keeps (ImgW b) m m') : ShaMemP b lb sc m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  have l1 := shaC_lens.1
  obtain ⟨l2, l3, l4, l5⟩ := shaP_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa160 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h4
  · unfold Loaded Memory.fetchBytes at h5 ⊢
    rw [l5] at h5 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h5
  · unfold Memory.readBytes at h6 ⊢
    rw [skeeps_range (off := 0x7238) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h6
  · unfold Memory.readBytes at h7 ⊢
    rw [skeeps_range (off := 0x71e0) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h7
  · exact (hl (off := 0x9dd8) (by decide)).trans h8
  · exact (hl (off := 0x9ef8) (by decide)).trans h9
  · exact (hl (off := 0x9f70) (by decide)).trans h10
  · exact (hl (off := 0x9f98) (by decide)).trans h11
  · exact (hl (off := 0x9df0) (by decide)).trans h12

theorem ShaMemM.keepW {b lb sr : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemM b lb sr m) (h : Keeps (ImgW b) m m') : ShaMemM b lb sr m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, r1, r2, r3⟩ := hm
  obtain ⟨l1, l2, l3, l4, l5⟩ := shaM_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa160 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h4
  · unfold Loaded Memory.fetchBytes at h5 ⊢
    rw [l5] at h5 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h5
  · unfold Memory.readBytes at h6 ⊢
    rw [skeeps_range (off := 0x716e) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h6
  · unfold Memory.readBytes at h7 ⊢
    rw [skeeps_range (off := 0xa01c) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]; exact h7
  · unfold Memory.readBytes at h8 ⊢
    rw [skeeps_range (off := 0xa170) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩)]
    exact h8
  · exact (hl (off := 0x9de0) (by decide)).trans h9
  · exact (hl (off := 0x9e70) (by decide)).trans h10
  · exact (hl (off := 0x9e78) (by decide)).trans h11
  · exact (hl (off := 0x9e90) (by decide)).trans h12
  · exact (hl (off := 0x9eb0) (by decide)).trans h13
  · exact (hl (off := 0x9f18) (by decide)).trans h14
  · exact (hl (off := 0x9f38) (by decide)).trans h15
  · exact (hl (off := 0x9fa0) (by decide)).trans h16
  · exact (hl (off := 0x9fb8) (by decide)).trans h17
  · exact (hl (off := 0x9fc8) (by decide)).trans h18
  · exact r1.keep h fun k hk => by
      rw [addr_toNat (by omega)]; rw [l1] at hk; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
  · exact r2.keep h fun k hk => by
      rw [addr_toNat (by omega)]; rw [l2] at hk; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
  · exact r3.keep h fun k hk => by
      rw [addr_toNat (by omega)]; rw [l3] at hk; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩

/-- All image facts `main` and its helpers use (`kb`: `libcrypto.so.3`'s base; `sr`, `sc`: the
`strrchr` and `strcspn` ifunc choices). -/
structure ShaMemAll (b lb kb sr sc : Word) (m : Memory) : Prop where
  st : ShaMem b lb m
  cl : ShaMemC b lb m
  dg : ShaMemD b lb kb m
  pr : ShaMemP b lb sc m
  mn : ShaMemM b lb sr m

theorem ShaMemAll.keepW {b lb kb sr sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemAll b lb kb sr sc m) (h : Keeps (ImgW b) m m') : ShaMemAll b lb kb sr sc m' :=
  ⟨hm.st.keepW hb h, hm.cl.keepW hb h, hm.dg.keepW hb h, hm.pr.keepW hb h, hm.mn.keepW hb h⟩

theorem ShaMemAll.keep {b lb kb sr sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemAll b lb kb sr sc m) (h : Keeps (ShaImg b) m m') : ShaMemAll b lb kb sr sc m' :=
  hm.keepW hb (imgW_img h)

end Silmaril.Elf.Link.Dyn.Sha256sum
