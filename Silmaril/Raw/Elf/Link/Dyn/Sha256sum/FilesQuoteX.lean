module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuoteN
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuoteStop
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CertQuoteX
public import Silmaril.Raw.Elf.Link.Dyn.ProcG.Cert
public import Silmaril.Raw.Elf.Link.Dyn.Cert.Frame
public import Silmaril.X86.Str9G.Thms

/-! # GNU `sha256sum`: gnulib's `quotef` on the extended process

`quotef` (`0x6950`) builds its `quoting_options` with SSE moves, so `Proc.proc` (image machine
`Open9`) stops at `0x6958` (`FilesQuoteStop`). Here the process is `procG Str9G.extendsOpen9`
(`ProcG`): the image runs on `Str9G`, which executes SSE data movement, and library calls keep
their contracts on the `MState` view.

PROVED (standard axioms):

* `qpro1`–`qpro5`: the 15 instructions `0x6950`–`0x698f` on `procG`, block certificates
  (`blk6950`, `blk6960`, via `ProcG.mustG_blkX_at`) for the integer code, `Str9G`'s SSE listing
  law (`step_of_listed_sse`, via `ProcG.mustG_step`) for `movdqa`/`movups`/`pxor`, and the call;
* **`quotef_proX`**: from a `QEntry` state to `0x6720` with `QAfter` (the saved `rbp`, the guard
  copy, the options `QOpts` expects — style 3, `quote_these_too` with only `:` — and the return
  address `0x6994`, all in `qproMem`);
* **`task_quotefX`**: `Task.quotefTail → Task.quotefX` (`quotef` on plain names on `procG`): the
  prologue on `procG`, then the `proc` run of the rest, lifted by `ProcG.mustG_of_mustQ`.

Assumed: the executable's base is 16-byte aligned (`movdqa` faults otherwise; the loader maps the
image at a page boundary, but `ExeLoaded` does not record it), and silmaril's `Sse9` semantics
of the SSE forms (a handwritten model of the SDM, as `Str9G` documents).

Open: `Task.quotefTail` (`proc`): `quotearg_n_options` from `QAfter` and `quotef`'s epilogue.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum
open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.ProcG
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams

set_option maxRecDepth 10000 in
theorem quoteX7_len : quoteX7Text.length = 393 := by decide

theorem ShaRO.codeRO {b lb : Word} {m : Memory} (h : ShaRO b lb m) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {v : Nat} {code : List Byte} (hv : 0x2000 ≤ v) (hend : v + code.length ≤ 0x2000 + 0x4d51) :
    CodeRO m (b + BitVec.ofNat 64 v) code := by
  obtain ⟨Fk, Fc, Fl, kb, ldb, res, ifn, m0, h1, h2, h3, h4, h5⟩ := h
  exact (codeRO_of_loaded h4 hv hend).keep h5 (fun k hk => by
    rw [addr_toNat (show b.toNat + v < 2 ^ 64 by omega)]; constructor <;> omega)

theorem ShaRO.readRo {b lb : Word} {m : Memory} (h : ShaRO b lb m) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {v : Nat} {l : List Byte} (hv : 0x7000 ≤ v) (hend : v + l.length ≤ 0x7000 + 0x1840)
    (h0 : 0 < l.length) (hp : plainOk shaFile shaRoPh shaSlots v l = true) :
    m.readBytes (b + BitVec.ofNat 64 v).toNat l.length = some l := by
  obtain ⟨Fk, Fc, Fl, kb, ldb, res, ifn, m0, h1, h2, h3, h4, h5⟩ := h
  rw [h5.readBytes (fun k hk => by
    rw [addr_toNat (show b.toNat + v < 2 ^ 64 by omega)]; constructor <;> omega)]
  obtain ⟨f, b', i, D, T, hf, hb', hi, -, hD, hT, himg⟩ := h4
  simp only [List.head?_cons, Option.some.injEq] at hf hb'
  subst hf hb'
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots h1 h2 h3, Option.some.injEq] at hD
  subst hD
  have hro : shaRoPh ∈ shaInfo.phs := by decide
  exact himg.readPlain hT hro rfl (by simpa [shaRoPh] using hv) (by simpa [shaRoPh] using hend) h0
    (acc := .read) rfl hp

/-- The 16 bytes of `quote_these_too[0..3]` in `.rodata` (`0x8340`): only `:` is set. -/
def qttConst : List Byte := ([0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).map (BitVec.ofNat 8)

theorem qtt_plain : plainOk shaFile shaRoPh shaSlots 0x8340 qttConst = true := by decide +kernel

theorem qtt_len : qttConst.length = 16 := rfl

theorem ShaRO.qtt {b lb : Word} {m : Memory} (h : ShaRO b lb m) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    m.readBytes (b + 0x8340#64).toNat 16 = some qttConst := by
  have := h.readRo hb (v := 0x8340) (l := qttConst) (by omega) (by rw [qtt_len]; omega) (by rw [qtt_len]; omega) qtt_plain
  rw [qtt_len] at this; exact this

abbrev XG : Silmaril.X86.Open9.isa.Extends Silmaril.X86.Str9G.isa :=
  Silmaril.X86.Str9G.extendsOpen9
abbrev XPS := GState Silmaril.X86.Str9G.GState

theorem xg_view (g : Silmaril.X86.Str9G.GState) : XG.view g = g.x.m := rfl
theorem xg_put (g : Silmaril.X86.Str9G.GState) (m : MState) :
    XG.put g m = { g with x := { g.x with m := m } } := rfl


abbrev mkX (c : State) (M : Memory) (xs : Silmaril.X86.Sse9.XFile) (tsc : Nat → Word) (cet : Bool)
    (g : Ghost) : XPS := ⟨⟨⟨⟨c, M⟩, xs⟩, tsc, cet⟩, g⟩

/-- The code facts of `quotef`'s chunk. -/
structure QCode (W : World) (b : Word) (M : Memory) : Prop where
  img : ∀ n, n < quoteX7Text.length → W.InImage (b + BitVec.ofNat 64 (0x681c + n)).toNat
  ld : Loaded M (b + BitVec.ofNat 64 0x681c) quoteX7Text
  ro : CodeRO M (b + BitVec.ofNat 64 0x681c) quoteX7Text

theorem QCode.store {W : World} {b : Word} {M : Memory} (h : QCode W b M) {a : Word} {k : Nat} {v : Word}
    (hw : M.Permitted .write a.toNat k) : QCode W b (storeMem M a k v) := by
  have hf : Frame M (storeMem M a k v) := by
    have := storeN_ok (v := v) hw
    unfold Silmaril.X86.Ext.storeN at this
    exact frame_write this
  exact ⟨h.img, loaded_frame h.ld h.ro hf, codeRO_frame h.ro hf⟩

set_option maxHeartbeats 1000000 in
theorem qpro1 {W : World} {b : Word} {Q : XPS → Prop} {c : State} {M : Memory}
    {xs : Silmaril.X86.Sse9.XFile} {tsc : Nat → Word} {cet : Bool} {g : Ghost}
    (hd : g.done = none) (hC : QCode W b M) (hrip : c.rip = b + 0x6950#64)
    (hw : M.Permitted .write (c.read .rsp - 8#64).toNat 8)
    (k : ∀ c1 : State, c1.rip = b + 0x6958#64 → c1.read .rsp = c.read .rsp - 0x48#64 →
      c1.read .rbp = c.read .rsp - 8#64 → (∀ r, r ≠ .rsp → r ≠ .rbp → c1.read r = c.read r) →
      c1.fsBase = c.fsBase →
      MustG XG W Q (mkX c1 (storeMem M (c.read .rsp - 8#64) 8 (c.read .rbp)) xs tsc cet g)) :
    MustG XG W Q (mkX c M xs tsc cet g) := by
  refine mustG_blkX_at XG blk6950 blk6950_ok hd hC.img hC.ld hC.ro (by show c.rip = _; rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6950, id]
  · refine k _ ?_ ?_ ?_ ?_ rfl
    · blk_simp [blk6950, hrip]
    · blk_simp [blk6950]; bv_omega
    · blk_simp [blk6950]
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
  · exact hw

/-- `quote_these_too[0..3]` as the 128-bit value `movdqa` loads. -/
def qttV : Silmaril.X86.Sse9.Xmm := 0x0400000000000000#128

theorem qtt_load {M : Memory} {a : Word} (h : M.readBytes a.toNat 16 = some qttConst) :
    Silmaril.X86.Sse9.load128 M a = some qttV := by
  simp only [Silmaril.X86.Sse9.load128, h, Option.map_some]
  decide

theorem store128_eq {M : Memory} {a : Word} {v : Silmaril.X86.Sse9.Xmm} {w : Word}
    (hw : M.Permitted .write a.toNat 16) (hv : Silmaril.X86.Sse9.le128 v = Silmaril.X86.Ext.leBytes w 16) :
    Silmaril.X86.Sse9.store128 M a v = some (storeMem M a 16 w) := by
  have := storeN_ok (v := w) hw
  unfold Silmaril.X86.Ext.storeN at this
  unfold Silmaril.X86.Sse9.store128
  rw [hv]; exact this

theorem le128_qtt : Silmaril.X86.Sse9.le128 qttV = Silmaril.X86.Ext.leBytes 0x0400000000000000#64 16 := by
  decide
theorem le128_zero : Silmaril.X86.Sse9.le128 0 = Silmaril.X86.Ext.leBytes 0#64 16 := by decide


set_option maxHeartbeats 1000000 in
/-- `0x6960`–`0x697b`: the stack guard at `rbp-8`, the style `3` at `rbp-0x40`, `rsi = rbp-0x40`. -/
theorem qpro3 {W : World} {b : Word} {Q : XPS → Prop} {c : State} {M : Memory}
    {xs : Silmaril.X86.Sse9.XFile} {tsc : Nat → Word} {cet : Bool} {g : Ghost}
    (hd : g.done = none) (hC : QCode W b M) (hrip : c.rip = b + 0x6960#64) {gv : Word}
    (hg : loadN M (c.fsBase + 0x28#64) 8 = some gv)
    (hw1 : M.Permitted .write (c.read .rbp - 8#64).toNat 8)
    (hw2 : M.Permitted .write (c.read .rbp - 0x40#64).toNat 8)
    (k : ∀ c1 : State, c1.rip = b + 0x697b#64 → c1.read .rsi = c.read .rbp - 0x40#64 →
      (∀ r, r ≠ .rax → r ≠ .rsi → c1.read r = c.read r) → c1.fsBase = c.fsBase →
      MustG XG W Q (mkX c1 (storeMem (storeMem M (c.read .rbp - 8#64) 8 gv) (c.read .rbp - 0x40#64) 8 3#64)
        xs tsc cet g)) :
    MustG XG W Q (mkX c M xs tsc cet g) := by
  have e1 : c.read .rbp + 0xfffffffffffffff8#64 = c.read .rbp - 8#64 := by bv_omega
  have e2 : c.read .rbp + 0xffffffffffffffc0#64 = c.read .rbp - 0x40#64 := by bv_omega
  refine mustG_blkX_at XG blk6960 blk6960_ok hd hC.img hC.ld hC.ro (by show c.rip = _; rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6960, id, e1, e2]
  all_goals try simp only [id] at *
  · rename_i v0 h0
    rw [hg] at h0; cases h0
    refine k _ ?_ ?_ ?_ rfl
    · blk_simp [blk6960, hrip]
    · blk_simp [blk6960, e2]
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
  · exact hw2
  · exact hw1
  · exact ⟨_, hg⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- One listed SSE instruction of `quotef`'s chunk. -/
theorem qsse {W : World} {b : Word} {Q : XPS → Prop} {c : State} {M : Memory}
    {xs : Silmaril.X86.Sse9.XFile} {tsc : Nat → Word} {cet : Bool} {g : Ghost}
    (hd : g.done = none) (hC : QCode W b M) {o l : Nat} {i : Silmaril.X86.Sse9.Instr}
    {c' : State} {xs' : Silmaril.X86.Sse9.XFile} {M' : Memory} (ho : o + l ≤ 393) (hl0 : 0 < l)
    (hrip : c.rip = b + BitVec.ofNat 64 (0x681c + o))
    (hdec : Silmaril.X86.Str9FsX.decodeSseL ((quoteX7Text.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Sse9.exec i c xs M (c.rip + BitVec.ofNat 64 l) = .ok c' xs' M')
    (k : MustG XG W Q (mkX c' M' xs' tsc cet g)) : MustG XG W Q (mkX c M xs tsc cet g) := by
  have hs : Silmaril.X86.Str9G.step ⟨⟨⟨c, M⟩, xs⟩, tsc, cet⟩ = some ⟨⟨⟨c', M'⟩, xs'⟩, tsc, cet⟩ :=
    Silmaril.X86.Str9G.step_of_listed_sse (g := ⟨⟨⟨c, M⟩, xs⟩, tsc, cet⟩) hC.ld
      (by show c.rip = _; rw [hrip, ripadd]) (by rw [quoteX7_len]; omega) hdec hx
  have hin : W.InImage c.rip.toNat := by rw [hrip]; exact hC.img o (by rw [quoteX7_len]; omega)
  refine mustG_step XG (s := mkX c M xs tsc cet g) (x' := ⟨⟨⟨c', M'⟩, xs'⟩, tsc, cet⟩) hd ?_ ?_ ?_
  · exact hin
  · exact hs
  · exact k

theorem rbp_addr (c : State) (next : Word) (d : BitVec 32) :
    (Silmaril.X86.Ext.Mem.ofReg .rbp none d).addr c next = c.read .rbp + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Base.value]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- `call quotearg_n_options` (`0x698f`). -/
theorem qpro5 {W : World} {b : Word} {Q : XPS → Prop} {c : State} {M : Memory}
    {xs : Silmaril.X86.Sse9.XFile} {tsc : Nat → Word} {cet : Bool} {g : Ghost}
    (hd : g.done = none) (hC : QCode W b M) (hrip : c.rip = b + 0x698f#64)
    (hw : M.Permitted .write (c.read .rsp - 8#64).toNat 8)
    (k : ∀ c1 : State, c1.rip = b + 0x6720#64 → c1.read .rsp = c.read .rsp - 8#64 →
      (∀ r, r ≠ .rsp → c1.read r = c.read r) → c1.fsBase = c.fsBase →
      MustG XG W Q (mkX c1 (pushMem M (c.read .rsp) (b + 0x6994#64)) xs tsc cet g)) :
    MustG XG W Q (mkX c M xs tsc cet g) := by
  have hin : W.InImage c.rip.toNat := by rw [hrip]; exact hC.img 371 (by rw [quoteX7_len]; omega)
  refine mustG_insn XG (s := mkX c M xs tsc cet g) (o := 371) (l := 5)
    (i := .ext8 (.base (.call 0xfffffd8c#32))) hd hin hC.ld (by show c.rip = _; rw [hrip, ripadd])
    (by rw [quoteX7_len]; omega) (by decide +kernel) ?_
  show WP (Silmaril.X86.Ext9.exec _ c M 5) _
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using hw)]
  simp only [WP_ok]
  rw [show c.rip + 5#64 = b + 0x6994#64 by rw [hrip]; bv_omega]
  refine k _ ?_ ?_ ?_ rfl
  · simp
  · simp
  · intro r hr; simp [hr]

theorem exec_movups {c : State} {xs : Silmaril.X86.Sse9.XFile} {M M' : Memory} {next r : Word}
    {d : BitVec 32} {a : Word} (ha : c.read .rbp + d.signExtend 64 = a) (hn : next = r)
    (h : Silmaril.X86.Sse9.store128 M a (xs .xmm0) = some M') :
    Silmaril.X86.Sse9.exec (.store .ups (.mem (Silmaril.X86.Ext.Mem.ofReg .rbp none d)) .xmm0) c xs M next =
      .ok { c with rip := r } xs M' := by
  subst hn
  have e : (Silmaril.X86.Ext.Mem.ofReg .rbp none d).addr c next = a := (rbp_addr c next d).trans ha
  simp [Silmaril.X86.Sse9.exec, Silmaril.X86.Sse9.Move.aligned, e, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `movdqa 0x19e0(%rip),%xmm0` (`0x6958`): `xmm0 = quote_these_too[0..3]`. -/
theorem qpro2 {W : World} {b : Word} {Q : XPS → Prop} {c : State} {M : Memory}
    {xs : Silmaril.X86.Sse9.XFile} {tsc : Nat → Word} {cet : Bool} {g : Ghost}
    (hd : g.done = none) (hC : QCode W b M) (hrip : c.rip = b + 0x6958#64)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hal : b.toNat % 16 = 0)
    (hq : M.readBytes (b + 0x8340#64).toNat 16 = some qttConst)
    (k : MustG XG W Q (mkX { c with rip := b + 0x6960#64 } M
      (Silmaril.Machine.RegisterFile.write xs .xmm0 qttV) tsc cet g)) :
    MustG XG W Q (mkX c M xs tsc cet g) := by
  have hn : c.rip + BitVec.ofNat 64 8 = b + 0x6960#64 := by rw [hrip]; bv_omega
  have ha : Silmaril.X86.Ext.Mem.addr (Silmaril.X86.Ext.Mem.ofRip 0x19e0#32) c (b + 0x6960#64) =
      b + 0x8340#64 := by
    simp only [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip]
    simp [Silmaril.X86.Ext.Base.value]
  have hm : Silmaril.X86.Sse9.misaligned (.mem (Silmaril.X86.Ext.Mem.ofRip 0x19e0#32)) c (b + 0x6960#64) = false := by
    simp only [Silmaril.X86.Sse9.misaligned, ha, bne_eq_false_iff_eq]
    rw [addr_toNat (v := 0x8340) (by omega)]; omega
  have hx : Silmaril.X86.Sse9.exec (.load .dqa .xmm0 (.mem (Silmaril.X86.Ext.Mem.ofRip 0x19e0#32))) c xs M
      (c.rip + BitVec.ofNat 64 8) = .ok { c with rip := b + 0x6960#64 }
        (Silmaril.Machine.RegisterFile.write xs .xmm0 qttV) M := by
    rw [hn]
    simp only [Silmaril.X86.Sse9.exec, hm, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      Silmaril.X86.Sse9.readX, ha, qtt_load hq]
  exact qsse hd hC (o := 316) (l := 8) (by omega) (by omega) (by rw [hrip]) (by decide +kernel) hx k

theorem exec_pxor0 {c : State} {xs : Silmaril.X86.Sse9.XFile} {M : Memory} {next r : Word}
    (hn : next = r) :
    Silmaril.X86.Sse9.exec (.pxor .xmm0 (.reg .xmm0)) c xs M next =
      .ok { c with rip := r } (Silmaril.Machine.RegisterFile.write xs .xmm0 0) M := by
  subst hn; exact Silmaril.X86.Sse9.exec_pxor_self _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x697b`–`0x698f`: `movups %xmm0,-0x38(%rbp)`, `pxor`, `movups %xmm0,-0x28(%rbp)`, `pxor`,
`movups %xmm0,-0x18(%rbp)`: the rest of the options. -/
theorem qpro4 {W : World} {b : Word} {Q : XPS → Prop} {c : State} {M : Memory}
    {xs : Silmaril.X86.Sse9.XFile} {tsc : Nat → Word} {cet : Bool} {g : Ghost}
    (hd : g.done = none) (hC : QCode W b M) (hrip : c.rip = b + 0x697b#64) (hx0 : xs .xmm0 = qttV)
    (hw1 : M.Permitted .write (c.read .rbp - 0x38#64).toNat 16)
    (hw2 : M.Permitted .write (c.read .rbp - 0x28#64).toNat 16)
    (hw3 : M.Permitted .write (c.read .rbp - 0x18#64).toNat 16)
    (k : ∀ xs' : Silmaril.X86.Sse9.XFile, MustG XG W Q (mkX { c with rip := b + 0x698f#64 }
      (storeMem (storeMem (storeMem M (c.read .rbp - 0x38#64) 16 0x0400000000000000#64)
        (c.read .rbp - 0x28#64) 16 0#64) (c.read .rbp - 0x18#64) 16 0#64) xs' tsc cet g)) :
    MustG XG W Q (mkX c M xs tsc cet g) := by
  refine qsse hd hC (o := 351) (l := 4) (by omega) (by omega) (by rw [hrip]) (by decide +kernel)
    (exec_movups (d := 0xffffffc8#32) (r := b + 0x697f#64) (by rw [show BitVec.signExtend 64 0xffffffc8#32 = 0xffffffffffffffc8#64 by decide]; bv_omega) (by rw [hrip]; bv_omega) (store128_eq hw1 (by rw [hx0]; exact le128_qtt))) ?_
  have hC1 := hC.store (v := 0x0400000000000000#64) hw1
  have hC2 := hC1.store (v := 0#64) (storeMem_permitted.2 hw2)
  have hC3 := hC2.store (v := 0#64) (storeMem_permitted.2 (storeMem_permitted.2 hw3))
  refine qsse hd hC1 (o := 355) (l := 4) (by omega) (by omega) rfl (by decide +kernel)
    (exec_pxor0 (r := b + 0x6983#64) (by bv_omega)) ?_
  refine qsse hd hC1 (o := 359) (l := 4) (by omega) (by omega) rfl (by decide +kernel)
    (exec_movups (d := 0xffffffd8#32) (r := b + 0x6987#64)
      (by change c.read .rbp + _ = _; rw [show BitVec.signExtend 64 0xffffffd8#32 = 0xffffffffffffffd8#64 by decide]; bv_omega)
      (by bv_omega) (store128_eq (storeMem_permitted.2 hw2) (by simp only [Silmaril.Machine.RegisterFile.write_same]; exact le128_zero))) ?_
  refine qsse hd hC2 (o := 363) (l := 4) (by omega) (by omega) rfl (by decide +kernel)
    (exec_pxor0 (r := b + 0x698b#64) (by bv_omega)) ?_
  refine qsse hd hC2 (o := 367) (l := 4) (by omega) (by omega) rfl (by decide +kernel)
    (exec_movups (d := 0xffffffe8#32) (r := b + 0x698f#64)
      (by change c.read .rbp + _ = _; rw [show BitVec.signExtend 64 0xffffffe8#32 = 0xffffffffffffffe8#64 by decide]; bv_omega)
      (by bv_omega) (store128_eq (storeMem_permitted.2 (storeMem_permitted.2 hw3))
        (by simp only [Silmaril.Machine.RegisterFile.write_same]; exact le128_zero))) ?_
  exact k _

/-- The memory `quotef`'s prologue leaves (`R` = `rsp` at entry, `rbp0` the caller's `rbp`, `gv`
the stack guard): saved `rbp`, the guard copy, the options (style 3, `quote_these_too` with only
`:`, no custom quotes) and the return address `0x6994`. -/
def qproMem (M : Memory) (R rbp0 gv b : Word) : Memory :=
  pushMem (storeMem (storeMem (storeMem (storeMem (storeMem (storeMem M (R - 8#64) 8 rbp0)
    (R - 0x10#64) 8 gv) (R - 0x48#64) 8 3#64) (R - 0x40#64) 16 0x0400000000000000#64)
    (R - 0x30#64) 16 0#64) (R - 0x20#64) 16 0#64) (R - 0x48#64) (b + 0x6994#64)

/-- **The state at `0x6720` after `quotef`'s prologue** (from the entry state `s`). -/
structure QAfter (b : Word) (s u : PState) : Prop where
  rip : u.m.core.rip = b + 0x6720#64
  rsp : u.m.core.read .rsp = s.m.core.read .rsp - 0x50#64
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rsi : u.m.core.read .rsi = s.m.core.read .rsp - 0x48#64
  other : ∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rsi → u.m.core.read r = s.m.core.read r
  fs : u.m.core.fsBase = s.m.core.fsBase
  g : u.g = s.g
  mem : ∃ gv, loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some gv ∧
    u.m.memory = qproMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp) gv b

/-- An image address is not in the stack room. -/
theorem img_room {W : World} {b : Word} {M : Memory} {sp : Word} {n : Nat} (hroom : Room W M sp n)
    (I : W.InImage = ShaImg b) {a k : Nat} (ha : ∀ j, j < k → ShaImg b (a + j)) (hk0 : 0 < k) {lo hi : Nat}
    (hlo : sp.toNat - n ≤ lo) (hhi : hi ≤ sp.toNat + 8) (hlh : lo < hi) : a + k ≤ lo ∨ hi ≤ a := by
  by_contra hc
  have hx := (hroom.2.2 (max a lo) (by omega) (by omega)).2.2
  have := ha (max a lo - a) (by omega)
  rw [show a + (max a lo - a) = max a lo by omega] at this
  exact hx (Or.inl (by rw [I]; exact this))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`quotef`'s prologue on the extended process** (`0x6950`–`0x698f`, with its five SSE moves):
from a `QEntry` state to `0x6720`, `QAfter`. Assumes the executable's base is 16-byte aligned (the
loader maps it at a page boundary), as `movdqa` needs. -/
theorem quotef_proX {E : Env} {W : World} {b lb : Word} {Q : XPS → Prop} {y : XPS} {p : List Byte}
    (hE : QEntry E W b lb (y.view XG) p) (hal : b.toNat % 16 = 0)
    (k : ∀ z : XPS, QAfter b (y.view XG) (z.view XG) → MustG XG W Q z) : MustG XG W Q y := by
  obtain ⟨⟨⟨⟨c0, M0⟩, xs0⟩, tsc, cet⟩, g0⟩ := y
  replace hE : QEntry E W b lb ⟨⟨c0, M0⟩, g0⟩ p := hE
  have hrip : c0.rip = b + 0x6950#64 := hE.rip
  have hroom : Room W M0 (c0.read .rsp) 2048 := hE.room
  generalize hR : c0.read .rsp = R at hroom
  have hd : g0.done = none := hE.done
  have hb := hE.imps.hb
  have I := hE.imps.img
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hC0 : QCode W b M0 :=
    ⟨fun n hn => sha_in' I hb (by rw [quoteX7_len] at hn; omega),
     hE.ro.loaded hb (by decide) (by rw [quoteX7_len]; omega) (by rw [quoteX7_len]; decide) quoteX7_plain,
     hE.ro.codeRO hb (by decide) (by rw [quoteX7_len]; omega)⟩
  have hw : ∀ d : Nat, 8 ≤ d → d ≤ 0x50 → ∀ k, k ≤ d → M0.Permitted .write (R - BitVec.ofNat 64 d).toNat k :=
    fun d h1 h2 k hk => room_perm hroom (Or.inr rfl) (by rw [sub_toNat (by omega) (by omega)]; omega)
      (by rw [sub_toNat (by omega) (by omega)]; omega)
  have hro0 : ShaRO b lb M0 := hE.ro
  have hq0 : M0.readBytes (b + 0x8340#64).toNat 16 = some qttConst := hro0.qtt hb
  have hgu : ∃ g, loadN M0 (c0.fsBase + 0x28#64) 8 = some g := hE.guard
  obtain ⟨gv, hgv⟩ := hgu
  have hR8 : ∀ d : Nat, d ≤ 0x50 → (R - BitVec.ofNat 64 d).toNat = R.toNat - d :=
    fun d hd => sub_toNat (by omega) (by omega)
  -- the stack writes miss the image and the guard
  have hq8 : ∀ j, j < 16 → ShaImg b ((b + 0x8340#64).toNat + j) := fun j hj => by
    rw [addr_toNat (v := 0x8340) (by omega)]; unfold ShaImg; omega
  have hgk : ∀ d : Nat, 8 ≤ d → d ≤ 0x50 → ∀ n, n ≤ d →
      (c0.fsBase + 0x28#64).toNat + 8 ≤ (R - BitVec.ofNat 64 d).toNat ∨
        (R - BitVec.ofNat 64 d).toNat + n ≤ (c0.fsBase + 0x28#64).toNat := by
    intro d h1 h2 n hn
    rw [hR8 d h2]
    by_contra hc
    rcases Nat.lt_or_ge (c0.fsBase + 0x28#64).toNat (R.toNat - d) with h | h
    · have := hE.guardk (R.toNat - d - (c0.fsBase + 0x28#64).toNat) (by omega)
      rw [show (c0.fsBase + 0x28#64).toNat + (R.toNat - d - (c0.fsBase + 0x28#64).toNat) = R.toNat - d by omega] at this
      exact (hroom.2.2 (R.toNat - d) (by omega) (by omega)).2.2 this
    · have := hE.guardk 0 (by omega)
      exact (hroom.2.2 (c0.fsBase + 0x28#64).toNat (by omega) (by omega)).2.2 (by simpa using this)
  -- 0x6950: push rbp; mov rbp,rsp; sub rsp,0x40
  refine qpro1 hd hC0 hrip (by rw [hR]; exact hw 8 (by omega) (by omega) 8 (by omega))
    (fun c1 h1rip h1rsp h1rbp h1o h1fs => ?_)
  rw [hR] at h1rsp h1rbp ⊢
  have hC1 := hC0.store (v := c0.read .rbp) (hw 8 (by omega) (by omega) 8 (by omega))
  have hq1 : (storeMem M0 (R - 8#64) 8 (c0.read .rbp)).readBytes (b + 0x8340#64).toNat 16 = some qttConst := by
    have hdis : (b + 0x8340#64).toNat + 16 ≤ (R - 8#64).toNat ∨ (R - 8#64).toNat + 8 ≤ (b + 0x8340#64).toNat := by
      rcases img_room hroom I hq8 (by omega) (lo := R.toNat - 8) (hi := R.toNat) (by omega) (by omega) (by omega) with h | h
      · left; rw [hR8 8 (by omega)]; exact h
      · right; rw [hR8 8 (by omega)]; omega
    rw [storeMem_read_ne hdis]; exact hq0
  -- 0x6958: movdqa
  refine qpro2 hd hC1 h1rip hb hal hq1 ?_
  have hg1 : loadN (storeMem M0 (R - 8#64) 8 (c0.read .rbp)) ({ c1 with rip := b + 0x6960#64 }.fsBase + 0x28#64) 8 =
      some gv := by
    show loadN _ (c1.fsBase + 0x28#64) 8 = _
    rw [h1fs, loadN_storeMem_ne (hgk 8 (by omega) (by omega) 8 (by omega)).symm]; exact hgv
  have e1 : ({ c1 with rip := b + 0x6960#64 } : State).read .rbp = R - 8#64 := h1rbp
  -- 0x6960: guard, style, rsi
  refine qpro3 hd hC1 rfl hg1 (by rw [e1, show R - 8#64 - 8#64 = R - BitVec.ofNat 64 0x10 by bv_omega]; exact hw 0x10 (by omega) (by omega) 8 (by omega))
    (by rw [e1, show R - 8#64 - 0x40#64 = R - BitVec.ofNat 64 0x48 by bv_omega]; exact hw 0x48 (by omega) (by omega) 8 (by omega))
    (fun c3 h3rip h3rsi h3o h3fs => ?_)
  rw [e1, show R - 8#64 - 8#64 = R - 0x10#64 by bv_omega, show R - 8#64 - 0x40#64 = R - 0x48#64 by bv_omega]
  rw [e1] at h3rsi
  have e3 : c3.read .rbp = R - 8#64 := (h3o .rbp (by decide) (by decide)).trans e1
  have hC3 := (hC1.store (a := R - 0x10#64) (v := gv) (hw 0x10 (by omega) (by omega) 8 (by omega))).store
    (a := R - 0x48#64) (v := 3#64) (hw 0x48 (by omega) (by omega) 8 (by omega))
  -- 0x697b: the SSE stores
  refine qpro4 hd hC3 h3rip (by simp)
    (by rw [e3, show R - 8#64 - 0x38#64 = R - BitVec.ofNat 64 0x40 by bv_omega]; exact hw 0x40 (by omega) (by omega) 16 (by omega))
    (by rw [e3, show R - 8#64 - 0x28#64 = R - BitVec.ofNat 64 0x30 by bv_omega]; exact hw 0x30 (by omega) (by omega) 16 (by omega))
    (by rw [e3, show R - 8#64 - 0x18#64 = R - BitVec.ofNat 64 0x20 by bv_omega]; exact hw 0x20 (by omega) (by omega) 16 (by omega))
    (fun xs' => ?_)
  rw [e3, show R - 8#64 - 0x38#64 = R - 0x40#64 by bv_omega, show R - 8#64 - 0x28#64 = R - 0x30#64 by bv_omega,
    show R - 8#64 - 0x18#64 = R - 0x20#64 by bv_omega]
  have e4 : ({ c3 with rip := b + 0x698f#64 } : State).read .rsp = R - 0x48#64 :=
    (h3o .rsp (by decide) (by decide)).trans h1rsp
  have hC4 := ((hC3.store (a := R - 0x40#64) (k := 16) (v := 0x0400000000000000#64)
    (hw 0x40 (by omega) (by omega) 16 (by omega))).store (a := R - 0x30#64) (k := 16) (v := 0#64)
    (hw 0x30 (by omega) (by omega) 16 (by omega))).store (a := R - 0x20#64) (k := 16) (v := 0#64)
    (hw 0x20 (by omega) (by omega) 16 (by omega))
  -- 0x698f: call quotearg_n_options
  refine qpro5 hd hC4 rfl
    (by rw [e4, show R - 0x48#64 - 8#64 = R - BitVec.ofNat 64 0x50 by bv_omega]; exact hw 0x50 (by omega) (by omega) 8 (by omega))
    (fun c5 h5rip h5rsp h5o h5fs => ?_)
  rw [e4]
  refine k (mkX c5 _ xs' tsc cet g0) ?_
  show QAfter b ⟨⟨c0, M0⟩, g0⟩ ⟨⟨c5, _⟩, g0⟩
  refine ⟨h5rip, ?_, ?_, ?_, ?_, ?_, rfl, gv, hgv, ?_⟩
  · show c5.read .rsp = c0.read .rsp - 0x50#64
    rw [h5rsp, e4, hR]; bv_omega
  · show c5.read .rbp = c0.read .rsp - 8#64
    rw [h5o .rbp (by decide), hR]; exact e3
  · show c5.read .rsi = c0.read .rsp - 0x48#64
    rw [h5o .rsi (by decide), hR]; exact h3rsi.trans (by bv_omega)
  · intro r hsp' hbp har hsi
    show c5.read r = c0.read r
    rw [h5o r hsp']; exact (h3o r har hsi).trans (h1o r hsp' hbp)
  · show c5.fsBase = c0.fsBase
    rw [h5fs]; exact h3fs.trans h1fs
  · show _ = qproMem M0 (c0.read .rsp) (c0.read .rbp) gv b
    rw [hR]; rfl

/-- A **plain** name: non-empty, every byte in gnulib's always-safe set (`quotef` shows it bare). -/
def QPlain (p : List Byte) : Prop := p ≠ [] ∧ ∀ c ∈ toSpec p, Silmaril.Apps.Sha256sum.isSafe c = true

/-- **`quotef` after its prologue** (open; on `proc`): from `0x6720` as the prologue leaves it
(`QAfter`), `quotearg_n_options (0, name, SIZE_MAX, &options)` and `quotef`'s epilogue
(`0x6994`: stack-guard check, `leave`, `ret`) return with `QExit` relative to `quotef`'s entry
state. Everything on this path is `Open9` code. -/
def Task.quotefTail (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (Q : PState → Prop) (s u : PState) (p : List Byte), QEntry E W b lb s p → QPlain p → QAfter b s u →
    (∀ t, QExit E W b s t p → MustQ W Q t) → MustQ W Q u

/-- **gnulib's `quotef` on a plain name, on the extended process** `procG Str9G.extendsOpen9`
(the statement of `Task.quotef`, over the image machine with SSE moves, for plain names). -/
def Task.quotefX (E : Env) (W : World) (b lb : Word) : Prop :=
  ∀ (Q : XPS → Prop) (y : XPS) (p : List Byte), QEntry E W b lb (y.view XG) p → QPlain p →
    (∀ z, QExit E W b (y.view XG) (z.view XG) p → MustG XG W Q z) → MustG XG W Q y

/-- **`Task.quotefX` from `Task.quotefTail`**: the SSE prologue on `procG` (`quotef_proX`), then the
`proc` run of the rest, lifted (`mustG_of_mustQ`). -/
theorem task_quotefX {E : Env} {W : World} {b lb : Word} (hal : b.toNat % 16 = 0)
    (hT : Task.quotefTail E W b lb) : Task.quotefX E W b lb := by
  intro Q y p hE hP k
  refine quotef_proX hE hal (fun z hA => ?_)
  have h := hT (fun t => ∀ x', XG.view x' = t.m → MustG XG W Q ⟨x', t.g⟩) (y.view XG) (z.view XG) p hE hP hA
    (fun t hX => .done fun x' hx' => k ⟨x', t.g⟩ (by
      have e : GState.view XG ⟨x', t.g⟩ = t := by
        show (⟨XG.view x', t.g⟩ : PState) = t; rw [hx']
      rw [e]; exact hX))
  exact mustG_of_mustQ XG rfl h

end Silmaril.Elf.Link.Dyn.Sha256sum
