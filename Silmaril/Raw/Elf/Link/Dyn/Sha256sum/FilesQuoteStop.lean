module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuote
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CertMem

/-! # GNU `sha256sum`: `quotef` stops on the process machine

`quotef` (`0x6950`) starts

```
6950: push %rbp; mov %rsp,%rbp; sub $0x40,%rsp
6958: movdqa 0x19e0(%rip),%xmm0      (the option word quote_these_too[0..3], from 0x8340)
6960: mov %fs:0x28,%rax ... movups %xmm0,-0x38(%rbp); pxor %xmm0,%xmm0; movups ... ×2
698f: call quotearg_n_options
```

It builds its `quoting_options` on the stack with SSE moves. The image machine of the process
(`Proc.step`: `Open9.step`) decodes none of `movdqa`, `movups`, `pxor`: neither `Ext8.decode`
nor `Ext9.decodeNew` reads the bytes at `0x6958`. So `Open9.step` is `none` there and the
process **stops** (`quotef_sse_step`, `sha_quotef_stops`): the only way `MustQ W Q` holds at
`0x6958` is that `Q` already holds there.

Every run of `quotef` passes `0x6958` (the first three instructions fall through), with `rsp`
below the caller's, where no `QExit` (a return: `rsp` = the caller's `+ 8`) can hold. Hence
`Task.quotef` holds only for worlds where no `QEntry` state exists: it is **not provable on the
current process machine**. Proving it needs an image machine that executes SSE moves (`Open9`
with `Sse9`'s XMM state), or a trusted treatment of these five instructions.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc

/-- The 15 bytes at `0x6958`: `movdqa 0x19e0(%rip),%xmm0` and the start of the next
instruction (the fetch window). -/
def quoteSseText : List Byte :=
  ([0x66, 0x0f, 0x6f, 0x05, 0xe0, 0x19, 0x00, 0x00, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00] :
    List Nat).map (BitVec.ofNat 8)

theorem quoteSse_plain : plainOk shaFile shaTextPh shaSlots 0x6958 quoteSseText = true := by
  decide +kernel

/-- Neither `Ext` nor `Ext8`'s new forms nor `Ext9`'s new forms decode the bytes at `0x6958`. -/
theorem quoteSse_undecodable :
    Silmaril.X86.Ext.decode quoteSseText = none ∧ Silmaril.X86.Open9.newBad quoteSseText = true ∧
      Silmaril.X86.Open9.rawNotEof quoteSseText = true ∧
      Silmaril.X86.Ext9.decodeNew quoteSseText = none := by
  decide +kernel

/-- Code of the text segment under `ShaRO` is loaded as in the file. -/
theorem ShaRO.loaded {b lb : Word} {m : Memory} (h : ShaRO b lb m) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {v : Nat} {code : List Byte} (hv : 0x2000 ≤ v) (hend : v + code.length ≤ 0x2000 + 0x4d51)
    (h0 : 0 < code.length) (hp : plainOk shaFile shaTextPh shaSlots v code = true) :
    Loaded m (b + BitVec.ofNat 64 v) code := by
  obtain ⟨Fk, Fc, Fl, kb, ldb, res, ifn, m0, h1, h2, h3, h4, h5⟩ := h
  have hl := text_of_loaded h1 h2 h3 h4 hv hend h0 hp
  unfold Loaded at hl ⊢
  rw [h5.fetchBytes (fun k hk => by rw [addr_toNat (show b.toNat + v < 2 ^ 64 by omega)]; constructor <;> omega)]
  exact hl

/-- **`Open9` has no step at `0x6958`.** -/
theorem quotef_sse_step {m : MState} {b : Word} (hl : Loaded m.memory (b + 0x6958#64) quoteSseText)
    (hrip : m.core.rip = b + 0x6958#64) : Silmaril.X86.Open9.step m = none := by
  obtain ⟨hn, hbad, hne, hnew⟩ := quoteSse_undecodable
  have hf : m.memory.fetchBytes m.core.rip.toNat 15 = some quoteSseText := by
    rw [hrip]; exact hl
  obtain ⟨more, hw, h8⟩ := Silmaril.X86.Open9.fetch8_undecodable_of hf (by decide) hn hbad hne
  have hlen := Silmaril.X86.fetchWindow_length_le m.memory Silmaril.X86.maxInstrLength m.core.rip.toNat
  rw [hw] at hlen
  have hmore : more = [] := by
    have : quoteSseText.length = 15 := by decide
    simp only [List.length_append, this, Silmaril.X86.maxInstrLength] at hlen
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hmore
  unfold Silmaril.X86.Open9.step
  rw [h8]
  simp [Silmaril.X86.Ext9.fetchNew, hw, hnew]

/-- **The process stops at `0x6958`**: `MustQ` there only holds by `Q` itself. -/
theorem sha_quotef_stops {W : World} {b lb : Word} {Q : PState → Prop} {s : PState}
    (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) (hd : s.g.done = none)
    (hro : ShaRO b lb s.m.memory) (hrip : s.m.core.rip = b + 0x6958#64) (h : MustQ W Q s) : Q s := by
  have hl : Loaded s.m.memory (b + 0x6958#64) quoteSseText :=
    hro.loaded hb (v := 0x6958) (by decide) (by decide) (by decide) quoteSse_plain
  have hs := quotef_sse_step hl hrip
  have hin : W.InImage s.m.core.rip.toNat := by
    rw [hrip]; exact sha_in' I hb (n := 0x6958) (by decide)
  cases h with
  | done hq => exact hq
  | step _ hns _ =>
    exact absurd (by simp only [proc, step, hd, hin, ↓reduceIte, hs]) hns

end Silmaril.Elf.Link.Dyn.Sha256sum
