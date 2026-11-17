module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemMain
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CertMainAll
public import Silmaril.Elf.Link.Dyn.Cert.Defs

/-! # GNU `sha256sum`: the code facts block certificates need, from the loader

* `codeRO_of_loaded`: any piece of the text segment (`PT_LOAD` with flags `r-x`) is not writable,
  so `CodeRO` (the extra hypothesis of `Cert.must_blk`) follows from the loader relation;
* `text_of_loaded`: any piece of text whose bytes `plainOk` checks is loaded;
* `ShaMainAll`, `shaMainAll_of_loaded`: every piece of `main` in `CertMainAll`, loaded and not writable.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc

/-- **Code in the text segment is not writable.** -/
theorem codeRO_of_loaded {Fk Fc Fl : Blob} {b kb lb ldb res : Word} {ifn : Word → Option Word}
    {lazy : Bool} {mem : Memory} (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res mem)
    {v : Nat} {code : List Byte} (hv : 0x2000 ≤ v) (hend : v + code.length ≤ 0x2000 + 0x4d51) :
    Cert.CodeRO mem (b + BitVec.ofNat 64 v) code := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, -, -, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  have htext : shaTextPh ∈ shaInfo.phs := by decide
  intro k hk
  obtain ⟨hwrap, -, -, hw, -⟩ := himg shaTextPh htext rfl (v + k) (by simp [shaTextPh]; omega)
    (by simp [shaTextPh]; omega)
  dsimp only at hwrap hw
  rw [addr_toNat (by omega)]
  rw [addr_toNat (by omega), ← Nat.add_assoc] at hw
  rw [hw]; simp [shaTextPh]

/-- **Any piece of the text segment whose bytes `plainOk` checks is loaded** (as code). -/
theorem text_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem)
    {v : Nat} {code : List Byte} (hv : 0x2000 ≤ v) (hend : v + code.length ≤ 0x2000 + 0x4d51)
    (h0 : 0 < code.length) (hp : plainOk shaFile shaTextPh shaSlots v code = true) :
    Loaded mem (b + BitVec.ofNat 64 v) code := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have htext : shaTextPh ∈ shaInfo.phs := by decide
  exact himg.readPlain (l := code) hT htext rfl (by simpa [shaTextPh] using hv)
    (by simpa [shaTextPh] using hend) h0 (acc := .execute) rfl hp

/-- **The code of all of `main`, piece by piece** (the pieces of `CertMainAll`): loaded and not
writable. -/
structure ShaMainAll (b : Word) (mem : Memory) : Prop where
  ld0 : Loaded mem (b + BitVec.ofNat 64 0x2750) mainAll0Text
  ro0 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x2750) mainAll0Text
  ld1 : Loaded mem (b + BitVec.ofNat 64 0x2952) mainAll1Text
  ro1 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x2952) mainAll1Text
  ld2 : Loaded mem (b + BitVec.ofNat 64 0x2b2c) mainAll2Text
  ro2 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x2b2c) mainAll2Text
  ld3 : Loaded mem (b + BitVec.ofNat 64 0x2d21) mainAll3Text
  ro3 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x2d21) mainAll3Text
  ld4 : Loaded mem (b + BitVec.ofNat 64 0x2f1a) mainAll4Text
  ro4 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x2f1a) mainAll4Text
  ld5 : Loaded mem (b + BitVec.ofNat 64 0x3113) mainAll5Text
  ro5 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x3113) mainAll5Text
  ld6 : Loaded mem (b + BitVec.ofNat 64 0x330f) mainAll6Text
  ro6 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x330f) mainAll6Text
  ld7 : Loaded mem (b + BitVec.ofNat 64 0x34f6) mainAll7Text
  ro7 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x34f6) mainAll7Text
  ld8 : Loaded mem (b + BitVec.ofNat 64 0x36ee) mainAll8Text
  ro8 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x36ee) mainAll8Text
  ld9 : Loaded mem (b + BitVec.ofNat 64 0x38eb) mainAll9Text
  ro9 : Cert.CodeRO mem (b + BitVec.ofNat 64 0x38eb) mainAll9Text

/-- `ShaMainAll` from the loader relation (each piece's `plainOk` is its own small kernel check). -/
theorem shaMainAll_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMainAll b mem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll0_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll1_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll2_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll3_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll4_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll5_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll6_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll7_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll8_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)
  · exact text_of_loaded hk hc hl h (by decide) (by decide +kernel) (by decide +kernel) mainAll9_plain
  · exact codeRO_of_loaded h (by decide) (by decide +kernel)

end Silmaril.Elf.Link.Dyn.Sha256sum
