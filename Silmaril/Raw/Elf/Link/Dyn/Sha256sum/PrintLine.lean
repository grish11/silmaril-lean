module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintName

/-! # sha256sum's output path: a whole result line

`sha_printLine`: from `0x2b8a` in `main` (the digest of one file computed) to `0x2c8a`, in text
mode, without `--tag` and `-z`, for a file name with no backslash, newline or carriage return,
`stdout` receives exactly `hex(digest) ++ "  " ++ name ++ "\n"`. It chains the escape test
(`sha_escChk`), the two `--tag` tests, the hex loop (`sha_hexLoop`), two inline `putc`s
(`sha_putSpace1`, `sha_putMark`), `print_filename` (`sha_printName`) and the final inline `putc`
of the delimiter (`sha_putDelim`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

theorem exec_movzb_rip (dst : Reg) (c : State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : loadN m (c.rip + BitVec.ofNat 64 l + d.signExtend 64) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movx false .d .b dst (.mem (.ofRip d))))) c m l =
      .ok { c.write dst (((v.setWidth 8).setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, h, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits,
    Silmaril.X86.Ext.Sz.write]

theorem exec_loadq_rip (dst : Reg) (c : State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : loadN m (c.rip + BitVec.ofNat 64 l + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (.ofRip d)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write]

theorem exec_stored_rbp (src : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read .rbp + d.signExtend 64).toNat 4) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.mov .d (.mem (.ofReg .rbp none d)) src))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.read .rbp + d.signExtend 64) 4 (((c.read src).setWidth 32).setWidth 64)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, ofReg_addr, storeN_ok h, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.bytes]

theorem exec_storeb_rbp (src : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read .rbp + d.signExtend 64).toNat 1) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.store .b (.mem (.ofReg .rbp none d)) src))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.read .rbp + d.signExtend 64) 1 (((c.read src).setWidth 8).setWidth 64)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeNarrow, ofReg_addr, storeN_ok h, Silmaril.X86.Ext.Narrow.bytes,
    Silmaril.X86.Ext.Narrow.bits]

theorem exec_cmpb0_rbp (c : State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : loadN m (c.read .rbp + d.signExtend 64) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.cmpI8 (.mem (.ofReg .rbp none d)) 0#8))) c m l =
      .ok { c with flags := Silmaril.X86.Ext.subFlagsN (v.setWidth 8) 0#8, rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits, ofReg_addr, h]

theorem resultN_xor_self {n : Nat} (x : BitVec n) : Silmaril.X86.Ext.AluOp.resultN .xor x x = 0#n := by
  simp [Silmaril.X86.Ext.AluOp.resultN]

theorem eval_shr64 : Silmaril.X86.Ext.Cond.eval
    (Silmaril.X86.Ext.ShiftOp.shr.flags (64#64) 1 (Silmaril.X86.Ext.subFlagsN 0#8 0#8)) .e = some false := by
  rfl

theorem add_neg_toNat {r : Word} {d : BitVec 32} {k : Nat} (hd : (d.signExtend 64).toNat = 2 ^ 64 - k)
    (hk : k ≤ r.toNat) (hk0 : 0 < k) : (r + d.signExtend 64).toNat = r.toNat - k := by
  rw [BitVec.toNat_add, hd]; have := r.isLt; omega

theorem off_d0 : (BitVec.signExtend 64 0xffffff30#32).toNat = 2 ^ 64 - 0xd0 := by decide
theorem off_c8 : (BitVec.signExtend 64 0xffffff38#32).toNat = 2 ^ 64 - 0xc8 := by decide
theorem off_d8 : (BitVec.signExtend 64 0xffffff28#32).toNat = 2 ^ 64 - 0xd8 := by decide
theorem off_ec : (BitVec.signExtend 64 0xffffff14#32).toNat = 2 ^ 64 - 0xec := by decide
theorem off_f8 : (BitVec.signExtend 64 0xffffff08#32).toNat = 2 ^ 64 - 0xf8 := by decide

/-- The frame slots of `main` the result line reads, at `rbp - 0xf8 … rbp - 0xc4`. -/
def SlotR (v : PState) (a : Nat) : Prop :=
  (v.m.core.read .rbp).toNat - 0xf8 ≤ a ∧ a < (v.m.core.read .rbp).toNat - 0xc4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The end of a result line** (`0x2bef` → `0x2c8a`): no `--tag`, so `putc (' ')`, `putc
(binary ? '*' : ' ')` (here `' '`), `print_filename (name, 0)` and `putc (delim)`. -/
theorem sha_lineTail {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc) (hP : PutcLaw E)
    (hD : StreamsDisj E)
    {Q : PState → Prop} {s0 v : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 v fr n saved) (hrip : v.m.core.rip = b + 0x2bef#64)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 64 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    (hv : StdVars E W lb v.m.memory)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64)
    (hslot : (v.m.core.read .rsp).toNat + 0xf8 ≤ (v.m.core.read .rbp).toNat)
    (htag : loadN v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32) 1 = some 0#64)
    {bv : Word} (hbin : loadN v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 4 = some bv)
    (hbv : bv.setWidth 32 = 0#32 ∨ bv.setWidth 32 = 0xffffffff#32)
    (hesc : loadN v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff08#32) 4 = some 0#64)
    {dl : Word} (hdl : loadN v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff14#32) 1 = some dl)
    {name : List Byte} (hname : CStr v.m.memory (v.m.core.read .r12) name)
    (hnk : ∀ j < name.length + 1, W.Kept ((v.m.core.read .r12).toNat + j))
    {st : St} (hst : StdoutIs E v.m.memory st)
    (k : ∀ w st', Body W (ShaMemP b lb sc) s0 w fr n saved → w.m.core.rip = b + 0x2c8a#64 →
      w.m.core.read .rsp = v.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, w.m.core.read r = v.m.core.read r) →
      StdoutIs E w.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      w.g.out ++ st'.buf = v.g.out ++ st.buf ++ ([0x20#8, 0x20#8] ++ name ++ [dl.setWidth 8]) →
      w.g.jobs = v.g.jobs → w.g.atexit = v.g.atexit → w.g.done = none →
      (w.g.inp = v.g.inp ∧ w.g.allocs = v.g.allocs ∧ w.g.heap = v.g.heap ∧
        w.g.files = v.g.files) → w.g.err = v.g.err →
      Keeps (fun a => W.Kept a ∨ (v.m.core.read .rsp).toNat ≤ a) v.m.memory w.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file v.m.memory f st'' → E.S.file w.m.memory f st'') →
      LibK E W v.m.memory w.m.memory → MustQ W Q w) :
    MustQ W Q v := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  have hroom := hB.room
  have hr1 := hroom.1
  have hu : (v.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by omega)
  set R := (v.m.core.read .rsp).toNat with hR
  set P := v.m.core.read .rbp with hPd
  have aec : (P + BitVec.signExtend 64 0xffffff14#32).toNat = P.toNat - 0xec := add_neg_toNat off_ec (by omega) (by decide)
  -- facts about `v`'s frame carry over to a later state that kept it
  have tr : ∀ (m : Memory) (d : BitVec 32) (j : Nat) (q : Nat), (P + d.signExtend 64).toNat = P.toNat - q →
      q ≤ 0xf8 → Keeps (fun a => W.Kept a ∨ R ≤ a) v.m.memory m →
      loadN m (P + d.signExtend 64) j = loadN v.m.memory (P + d.signExtend 64) j := by
    intro m d j q hq hq8 hk
    exact Keeps.loadN hk (fun i hi => Or.inr (by rw [hq]; omega))
  -- `cmp byte [rbp - 0xd0], 0; jne` (no `--tag`)
  refine must_listed (o := 101) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_cmpb0_rbp _ _ _ _ _ htag]
  simp only [WP_ok, ripadd, hrip]
  refine must_listed (o := 108) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [eval_ne_sub]
  -- `putc (' ')`
  refine sha_putSpace1 I hP hD (hB.of_eq rfl rfl rfl rfl) rfl hv hfk hlo hfw (by omega) hn hsv hal hrel hst ?_
  intro v1 st1 hB1 hr1' hs1 hc1 hst1 he1 hrd1 hef1 hg1 ho1 hj1 ha1 hd1 hi1 hie1 hk1 hf1 hL1
  have hs1' : v1.m.core.read .rsp = v.m.core.read .rsp := hs1
  have hc1' : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v1.m.core.read r = v.m.core.read r := hc1
  have hk1' : Keeps (fun a => W.Kept a ∨ R ≤ a) v.m.memory v1.m.memory := hk1
  have hp1 : v1.m.core.read .rbp = P := hc1' .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])
  -- `putc (binary > 0 ? '*' : ' ')`
  refine sha_putMark I hP hD hB1 hr1' (bv := bv)
    (by rw [hp1, tr _ _ _ 0xc8 (add_neg_toNat off_c8 (by omega) (by decide)) (by decide) hk1']; exact hbin) hbv
    (hv.keep (hk1'.mono fun a ha => Or.inl ha)) hfk hlo hfw (by omega) hn hsv hal hrel hst1 ?_
  intro v2 st2 hB2 hr2 hs2 hc2 hst2 he2 hrd2 hef2 hg2 ho2 hj2 ha2 hd2 hi2 hie2 hk2 hf2 hL2
  have hk2' : Keeps (fun a => W.Kept a ∨ R ≤ a) v.m.memory v2.m.memory := hk1'.trans (by rw [hs1'] at hk2; exact hk2)
  have hp2 : v2.m.core.read .rbp = P := by rw [hc2 .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hp1]
  have h12 : v2.m.core.read .r12 = v.m.core.read .r12 := by
    rw [hc2 .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]), hc1' .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]
  -- `print_filename (name, 0)`
  refine sha_printName I (hB2.of_eq rfl rfl rfl rfl) hr2
    (by rw [hp2, tr _ _ _ 0xf8 (add_neg_toNat off_f8 (by omega) (by decide)) (by decide) hk2']; exact hesc)
    (hv.keep (hk2'.mono fun a ha => Or.inl ha)) hlo hfr hn hsv hal hrel (name := name)
    ⟨hname.1, by rw [h12, hk2'.readBytes (fun j hj => Or.inl (hnk j hj))]; exact hname.2⟩
    (by rw [h12]; exact hnk) hst2 ?_
  intro v3 st3 hB3 hr3 hs3 hc3 hst3 he3 hrd3 hef3 hg3 ho3 hj3 ha3 hd3 hi3 hie3 hk3 hf3 hL3
  have hk3' : Keeps (fun a => W.Kept a ∨ R ≤ a) v.m.memory v3.m.memory :=
    hk2'.trans (by rw [hs2, hs1'] at hk3; exact hk3)
  have hp3 : v3.m.core.read .rbp = P := by rw [hc3 .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hp2]
  -- `putc (delim)`
  refine sha_putDelim I hP hD hB3 hr3 (dl := dl)
    (by rw [hp3, tr _ _ _ 0xec aec (by decide) hk3']; exact hdl)
    (by rw [hp3, aec]; have := hroom.2.2; omega)
    (hv.keep (hk3'.mono fun a ha => Or.inl ha)) hfk hlo hfw (by omega) hn hsv hal hrel hst3 ?_
  intro v4 st4 hB4 hr4 hs4 hc4 hst4 he4 hrd4 hef4 hg4 ho4 hj4 ha4 hd4 hi4 hie4 hk4 hf4 hL4
  have hk4' : Keeps (fun a => W.Kept a ∨ R ≤ a) v.m.memory v4.m.memory :=
    hk3'.trans (by rw [hs3, hs2, hs1'] at hk4; exact hk4)
  refine k v4 st4 hB4 hr4 (by rw [hs4, hs3, hs2, hs1']) (fun r hr => ?_) hst4 (by rw [he4, he3, he2, he1])
    (by rw [hrd4, hrd3, hrd2, hrd1]) (by rw [hef4, hef3, hef2, hef1]) (by rw [hg4, hg3, hg2, hg1]) ?_ (by rw [hj4, hj3, hj2, hj1])
    (by rw [ha4, ha3, ha2, ha1]) hd4 ⟨by rw [hi4.1, hi3.1, hi2.1, hi1.1], by rw [hi4.2.1, hi3.2.1, hi2.2.1, hi1.2.1], by rw [hi4.2.2.1, hi3.2.2.1, hi2.2.2.1, hi1.2.2.1], by rw [hi4.2.2.2, hi3.2.2.2, hi2.2.2.2, hi1.2.2.2]⟩ (by rw [hie4, hie3, hie2, hie1])
    hk4'
    (fun f s'' hne hf => hf4 f s'' hne (hf3 f s'' hne (hf2 f s'' hne (hf1 f s'' hne hf))))
    (hL1.trans (hL2.trans (hL3.trans hL4)))
  · exact (hc4 r hr).trans ((hc3 r hr).trans ((hc2 r hr).trans (hc1' r hr)))
  · rw [ho4, ho3, ho2, ho1]; simp

set_option maxRecDepth 100000 in
/-- **Back to `main`'s loop** (`0x2c8a` → `0x2b57`): `movzx eax, byte [rbp - 0xd8]; jmp`. -/
theorem sha_lineRet {W : World} {b lb sc : Word} (hI : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {s0 v : PState} {fr n : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 v fr n saved) (hrip : v.m.core.rip = b + 0x2c8a#64)
    {rv : Word} (hrv : loadN v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff28#32) 1 = some rv)
    (k : ∀ w, Body W (ShaMemP b lb sc) s0 w fr n saved → w.m.core.rip = b + 0x2b57#64 →
      (∀ r, r ≠ .rax → w.m.core.read r = v.m.core.read r) →
      w.m.core.read .rax = ((rv.setWidth 8).setWidth 32).setWidth 64 →
      w.m.memory = v.m.memory → w.g = v.g → MustQ W Q w) :
    MustQ W Q v := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' hI hb hn
  refine must_listed (o := 256) shaP_listing_ok.1 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_movzb_rbp .rax _ _ _ _ rv hrv]
  simp only [WP_ok, ripadd, hrip]
  refine must_listed (o := 263) shaP_listing_ok.1 rfl hB.done (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep []
  refine k _ (hB.of_eq rfl (by simp) rfl rfl) rfl (fun r hr => ?_) (by simp) rfl rfl
  show Silmaril.Machine.RegisterFile.write v.m.core.regs .rax _ r = _
  rw [Silmaril.Machine.RegisterFile.write_other _ _ _ _ hr]; rfl

/-- The two frame slots the result line writes: the escape flag (`rbp - 0xf8`, four bytes) and
the delimiter (`rbp - 0xec`). -/
def StoredR (P : Word) (a : Nat) : Prop := (P.toNat - 0xf8 ≤ a ∧ a < P.toNat - 0xf4) ∨ a = P.toNat - 0xec

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The start of a result line** (`0x2b8a` → `0x2bc8`, the hex loop's head): the line
delimiter `'\n'` is kept at `rbp - 0xec` and the escape flag cleared; the name needs no
escaping (`sha_escChk`); no `--tag`; `digest_hex_bytes / 2 = 32` bytes to print, from `r13 = 0`. -/
theorem sha_lineHead {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x2b8a#64)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 64 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0)
    (hdelim : loadN u.m.memory (b + 0xa01c#64) 1 = some 0x0a#64)
    (hlen : loadN u.m.memory (b + 0xa178#64) 8 = some 64#64)
    (hslot : (u.m.core.read .rsp).toNat + 0xf8 ≤ (u.m.core.read .rbp).toNat)
    (hslot2 : (u.m.core.read .rbp).toNat - 0xc4 + sv ≤ (s0.m.core.read .rsp).toNat)
    (htag : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32) 1 = some 0#64)
    {name : List Byte} (hname : CStr u.m.memory (u.m.core.read .r12) name)
    (hnr : ∀ c ∈ name, c ∉ rejectBytes)
    (hnk : ∀ j < name.length + 1, W.Kept ((u.m.core.read .r12).toNat + j))
    (hnp : ∀ j < name.length + 1, ¬ E.S.priv u.m.memory ((u.m.core.read .r12).toNat + j))
    (k : ∀ w, Body W (ShaMemP b lb sc) s0 w fr n saved → w.m.core.rip = b + 0x2bc8#64 →
      w.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], w.m.core.read r = u.m.core.read r) →
      w.m.core.read .r13 = 0#64 →
      (∀ f st, E.S.file u.m.memory f st → E.S.file w.m.memory f st) → w.g = u.g →
      loadN w.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff08#32) 4 = some 0#64 →
      loadN w.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff14#32) 1 = some 0x0a#64 →
      Keeps (fun a => W.Kept a ∨ ((u.m.core.read .rsp).toNat ≤ a ∧ ¬ StoredR (u.m.core.read .rbp) a))
        u.m.memory w.m.memory → LibK E W u.m.memory w.m.memory → MustQ W Q w) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  have hroom := hB.room
  have hr1 := hroom.1
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by omega)
  set P := u.m.core.read .rbp with hPd
  have af8 : (P + BitVec.signExtend 64 0xffffff08#32).toNat = P.toNat - 0xf8 := add_neg_toNat off_f8 (by omega) (by decide)
  have aec : (P + BitVec.signExtend 64 0xffffff14#32).toNat = P.toNat - 0xec := add_neg_toNat off_ec (by omega) (by decide)
  have ad0 : (P + BitVec.signExtend 64 0xffffff30#32).toNat = P.toNat - 0xd0 := add_neg_toNat off_d0 (by omega) (by decide)
  have pw1 : u.m.memory.Permitted .write (P + BitVec.signExtend 64 0xffffff08#32).toNat 4 :=
    room_perm hroom (Or.inr rfl) (by rw [af8]; omega) (by rw [af8]; omega)
  have pw2 : u.m.memory.Permitted .write (P + BitVec.signExtend 64 0xffffff14#32).toNat 1 :=
    room_perm hroom (Or.inr rfl) (by rw [aec]; omega) (by rw [aec]; omega)
  -- `movzx eax, byte [delim]; xor edx, edx; mov [rbp - 0xf8], edx; mov [rbp - 0xec], al`
  refine must_listed (o := 0) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  rw [exec_movzb_rip .rax _ _ _ _ _ (by
    rw [hrip, show b + 0x2b8a#64 + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x748b#32 = b + 0xa01c#64 by
      simp only [BitVec.add_assoc]; rfl]
    exact hdelim)]
  have e10 : (((0x0a#64 : Word).setWidth 8).setWidth 32).setWidth 64 = 0x0a#64 := by decide
  simp only [WP_ok, ripadd, hrip, e10]
  refine must_listed (o := 7) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine (by rw [ripadd]) ?_
  xstep [resultN_xor_self]
  refine must_gen (fun x => x.m.core.rip = b + 0x2b93#64 ∧ x.m.core.read .rax = 0x0a#64 ∧
      x.m.core.read .rdx = 0#64 ∧ x.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, x.m.core.read r = u.m.core.read r) ∧
      x.m.memory = u.m.memory ∧ x.g = u.g ∧ x.m.core.fsBase = u.m.core.fsBase)
    ⟨rfl, by simp, by simp, by simp, fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro x ⟨hxr, hxa, hxd, hxsp, hxc, hxm, hxg, hxf⟩
  have hxp : x.m.core.read .rbp = P := hxc .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])
  have hBx : Body W (ShaMemP b lb sc) s0 x fr n saved := hB.of_eq hxm hxsp hxf (by rw [hxg])
  refine must_listed (o := 9) shaP_listing_ok.1 rfl hBx.done (by rw [hxr]; exact hin _ (by decide))
    hBx.mem.printLine (by rw [hxr, BitVec.add_assoc]; rfl) ?_
  rw [exec_stored_rbp .rdx _ _ _ _ (by rw [hxp, hxm]; exact pw1)]
  have e0 : (BitVec.setWidth 64 (BitVec.setWidth 32 (0#64 : Word))) = 0#64 := by decide
  simp only [WP_ok, hxd, hxp, e0, hxr, ripadd]
  have hm1 : ShaMemP b lb sc (storeMem x.m.memory (P + BitVec.signExtend 64 0xffffff08#32) 4 0#64) :=
    shaMemP_keep I.img I.hb _ _ hBx.mem (storeMem_keeps fun a ha => by
      rw [af8]; by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 (Or.inl ha))
  refine must_gen (fun y => y.m.core.rip = b + 0x2b99#64 ∧ (∀ r, y.m.core.read r = x.m.core.read r) ∧
      y.m.memory = storeMem x.m.memory (P + BitVec.signExtend 64 0xffffff08#32) 4 0#64 ∧ y.g = x.g ∧
      y.m.core.fsBase = x.m.core.fsBase) ⟨rfl, fun r => rfl, rfl, rfl, rfl⟩ ?_
  rintro y ⟨hyr, hyc, hym, hyg, hyf⟩
  refine must_listed (o := 15) shaP_listing_ok.1 rfl (by rw [hyg]; exact hBx.done) (by rw [hyr]; exact hin _ (by decide))
    (hym ▸ hm1.printLine) (by rw [hyr, BitVec.add_assoc]; rfl) ?_
  rw [exec_storeb_rbp .rax _ _ _ _ (by rw [hyc, hxp, hym]; exact storeMem_permitted.2 (hxm ▸ pw2))]
  have e1 : (((0x0a#64 : Word).setWidth 8).setWidth 64) = 0x0a#64 := by decide
  simp only [WP_ok, hyc, hxa, hxp, e1, ripadd, hym, hyr]
  have hm2 : ShaMemP b lb sc (storeMem (storeMem x.m.memory (P + BitVec.signExtend 64 0xffffff08#32) 4 0#64)
      (P + BitVec.signExtend 64 0xffffff14#32) 1 0x0a#64) :=
    shaMemP_keep I.img I.hb _ _ hm1 (storeMem_keeps fun a ha => by
      rw [aec]; by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 (Or.inl ha))
  refine must_listed (o := 21) shaP_listing_ok.1 rfl (by rw [hyg]; exact hBx.done) (hin _ (by decide))
    hm2.printLine (by rw [ripadd]) ?_
  xstep [hyc, hxa]
  refine must_listed (o := 23) shaP_listing_ok.1 rfl (by rw [hyg]; exact hBx.done) (hin _ (by decide))
    hm2.printLine (by rw [ripadd]) ?_
  xstep [eval_e_sub]
  -- the escape test
  refine must_gen (fun z => z.m.core.rip = b + 0x35b6#64 ∧ (∀ r, z.m.core.read r = x.m.core.read r) ∧
      z.m.memory = storeMem (storeMem x.m.memory (P + BitVec.signExtend 64 0xffffff08#32) 4 0#64)
        (P + BitVec.signExtend 64 0xffffff14#32) 1 0x0a#64 ∧ z.g = x.g ∧
      z.m.core.fsBase = x.m.core.fsBase) ⟨rfl, fun r => hyc r, rfl, hyg, hyf⟩ ?_
  rintro z ⟨hzr, hzc, hzm, hzg, hzf⟩
  have hB1 : Body W (ShaMemP b lb sc) s0
      ⟨⟨x.m.core, storeMem x.m.memory (P + BitVec.signExtend 64 0xffffff08#32) 4 0#64⟩, x.g⟩ fr n saved :=
    BodyX.store (shaMemP_keep I.img I.hb) hBx (by omega) (fun p hp => (hsv p hp).1)
      (by rw [af8]; omega) (by rw [af8]; omega) rfl rfl rfl rfl
  have hBz : Body W (ShaMemP b lb sc) s0 z fr n saved :=
    BodyX.store (shaMemP_keep I.img I.hb) hB1 (by omega) (fun p hp => (hsv p hp).1)
      (by rw [aec]; omega) (by rw [aec]; omega) hzm (hzc .rsp) hzf (by rw [hzg])
  have hkz : Keeps (fun a => W.Kept a ∨ ((u.m.core.read .rsp).toNat ≤ a ∧ ¬ StoredR P a) ∨ a < E.S.lo)
      u.m.memory z.m.memory := by
    rw [hzm, hxm]
    refine (storeMem_keeps fun a ha => ?_).trans (storeMem_keeps fun a ha => ?_)
    · rw [af8]; rcases ha with h | ⟨h1, h2⟩ | h
      · by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 h
      · unfold StoredR at h2; omega
      · omega
    · rw [aec]; rcases ha with h | ⟨h1, h2⟩ | h
      · by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 h
      · unfold StoredR at h2; omega
      · omega
  have h12z : z.m.core.read .r12 = u.m.core.read .r12 := by
    rw [hzc, hxc .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]
  have hnz : CStr z.m.memory (z.m.core.read .r12) name :=
    ⟨hname.1, by rw [h12z, hkz.readBytes (fun j hj => Or.inl (hnk j hj))]; exact hname.2⟩
  have hpz : E.S.priv z.m.memory = E.S.priv u.m.memory :=
    E.S.priv_local _ _ fun a ha => hkz a (Or.inr (Or.inr ha))
  refine sha_escChk I hBz hzr hlo (by omega) hn hsv hal hnz hnr (by rw [h12z]; exact hnk)
    (by rw [h12z, hpz]; exact hnp) ?_
  intro w hBw hwr hws hwc hwf hwg hwn hwk hwL
  have hLw : LibK E W u.m.memory w.m.memory :=
    ((LibK.refl E W _).high (hkz.mono fun a ha => Or.inr (Or.inr ha))).trans hwL
  have hzs : z.m.core.read .rsp = u.m.core.read .rsp := by rw [hzc, hxsp]
  have hwp : w.m.core.read .rbp = P := by
    rw [hwc .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hzc, hxp]
  have hkw : Keeps (fun a => W.Kept a ∨ ((u.m.core.read .rsp).toNat ≤ a ∧ ¬ StoredR P a)) u.m.memory w.m.memory :=
    (hkz.mono fun a ha => by rcases ha with h | h <;> simp_all).trans
      (hwk.mono fun a ha => by rw [hzs]; rcases ha with h | h; exact Or.inl h; exact Or.inr h.1)
  have hdw := hBw.done
  -- `cmp byte [rbp - 0xd0], 0; jne` (no `--tag`)
  refine must_listed (o := 29) shaP_listing_ok.1 rfl hdw (by rw [hwr]; exact hin _ (by decide))
    hBw.mem.printLine (by rw [hwr, BitVec.add_assoc]; rfl) ?_
  rw [exec_cmpb0_rbp _ _ _ _ _ (by
    rw [hwp, hkw.loadN (fun j hj => Or.inr ⟨by rw [ad0]; omega, by unfold StoredR; rw [ad0]; omega⟩)]
    exact htag)]
  simp only [WP_ok, ripadd, hwr]
  refine must_listed (o := 36) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hBw.mem.printLine
    (by rw [ripadd]) ?_
  xstep [eval_ne_sub]
  -- `mov rax, [digest_hex_bytes]; shr rax, 1; je; xor r13d, r13d`
  have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by have := I.hb; omega)
  have hlenw : loadN w.m.memory (b + 0xa178#64) 8 = some 64#64 := by
    rw [loadN_keeps hkw (fun j hj => Or.inl (Or.inl (show W.InImage _ by
      rw [I.img, e78]; exact ⟨by omega, by omega⟩)))]
    exact hlen
  refine must_listed (o := 42) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hBw.mem.printLine
    (by rw [ripadd]) ?_
  rw [exec_loadq_rip .rax _ _ _ _ _ (by
    rw [show b + BitVec.ofNat 64 (11146 + 36 + 6) + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x75bd#32 =
      b + 0xa178#64 by simp only [BitVec.add_assoc]; rfl]
    exact hlenw)]
  simp only [WP_ok, ripadd]
  refine must_listed (o := 49) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hBw.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.ShiftOp.result]
  refine must_listed (o := 52) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hBw.mem.printLine
    (by rw [BitVec.add_assoc]; rfl) ?_
  xstep [eval_shr64]
  refine must_listed (o := 54) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hBw.mem.printLine
    (by rw [BitVec.add_assoc]; rfl) ?_
  xstep [resultN_xor_self]
  refine must_listed (o := 57) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hBw.mem.printLine
    (by rw [BitVec.add_assoc]; rfl) ?_
  xstep []
  -- the stored slots
  have pr1 : u.m.memory.Permitted .read (P + BitVec.signExtend 64 0xffffff08#32).toNat 4 :=
    room_perm hroom (Or.inl rfl) (by rw [af8]; omega) (by rw [af8]; omega)
  have pr2 : u.m.memory.Permitted .read (P + BitVec.signExtend 64 0xffffff14#32).toNat 1 :=
    room_perm hroom (Or.inl rfl) (by rw [aec]; omega) (by rw [aec]; omega)
  have hzw : ∀ (a : Word) (j : Nat), (u.m.core.read .rsp).toNat ≤ a.toNat →
      loadN w.m.memory a j = loadN z.m.memory a j := fun a j ha =>
    hwk.loadN (fun i hi => Or.inr (by rw [hzs]; omega))
  have hs1 : loadN w.m.memory (P + BitVec.signExtend 64 0xffffff08#32) 4 = some 0#64 := by
    rw [hzw _ _ (by rw [af8]; omega), hzm]
    simp only [loadN]
    rw [storeMem_read_ne (by rw [af8, aec]; omega), storeMem_read (hxm ▸ pr1)]
    simp [Silmaril.X86.Ext.leValue_leBytes]
  have hs2 : loadN w.m.memory (P + BitVec.signExtend 64 0xffffff14#32) 1 = some 0x0a#64 := by
    rw [hzw _ _ (by rw [aec]; omega), hzm]
    simp only [loadN]
    rw [storeMem_read (storeMem_permitted.2 (hxm ▸ pr2))]
    simp [Silmaril.X86.Ext.leValue_leBytes]
  refine k _ (hBw.of_eq rfl (by simp) rfl rfl) rfl (by simp [hws, hzs]) (fun r hr => ?_) (by simp)
    (fun f st h => hwf f st ((E.S.local_ _ _ _ _ (hkz.mono fun a ha => Or.inr (Or.inr
      (E.S.foot_lo _ _ _ _ h ha))) h).1)) (by rw [hwg, hzg, hxg]) hs1 hs2 hkw hLw
  have hcs : r ∈ Silmaril.X86.sysv64.calleeSaved := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Silmaril.X86.sysv64_calleeSaved]
  have h1 : r ≠ .rax := by
    intro h; subst h; simp at hr
  have h2 : r ≠ .r13 := by
    intro h; subst h; simp at hr
  show Silmaril.Machine.RegisterFile.write (Silmaril.Machine.RegisterFile.write w.m.core.regs .rax _) .r13 _ r = _
  rw [Silmaril.Machine.RegisterFile.write_other _ _ _ _ h2, Silmaril.Machine.RegisterFile.write_other _ _ _ _ h1]
  exact (hwc r hcs).trans ((hzc r).trans (hxc r hcs))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **A result line of `sha256sum`** (`0x2b8a` → `0x2c8a`, text mode, no `--tag`, no `-z`):
for a file name with no backslash, newline or carriage return, `stdout` receives exactly
`hex(digest) ++ "  " ++ name ++ "\n"`; the caller's frame is kept except the two slots the line
writes (`StoredR`), and every other stream is kept. `sha_lineRet` continues to `0x2b57`.
`PutcLaw` (the strengthened inline-`putc` law) and `StreamsDisj` (distinct streams own disjoint
bytes) are assumptions on the stream representation. -/
theorem sha_printLine {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc) (hP : PutcLaw E)
    (hD : StreamsDisj E)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x2b8a#64)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 64 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    (hv : StdVars E W lb u.m.memory)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64)
    -- the program's globals: the line delimiter `'\n'` (no `-z`) and `digest_hex_bytes = 64`
    (hdelim : loadN u.m.memory (b + 0xa01c#64) 1 = some 0x0a#64)
    (hlen : loadN u.m.memory (b + 0xa178#64) 8 = some 64#64)
    -- `main`'s frame: the slots at `rbp - 0xf8 … rbp - 0xc4` lie in it
    (hslot : (u.m.core.read .rsp).toNat + 0xf8 ≤ (u.m.core.read .rbp).toNat)
    (hslot2 : (u.m.core.read .rbp).toNat - 0xc4 + sv ≤ (s0.m.core.read .rsp).toNat)
    (htag : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32) 1 = some 0#64)
    {bv : Word} (hbin : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 4 = some bv)
    (hbv : bv.setWidth 32 = 0#32 ∨ bv.setWidth 32 = 0xffffffff#32)
    (hr14 : u.m.core.read .r14 = b + 0x7238#64)
    -- the digest (`rbx`, 32 bytes, in the frame) and the name (`r12`)
    {dg : List Byte} (hdg : u.m.memory.readBytes (u.m.core.read .rbx).toNat 32 = some dg)
    (hdgs : (u.m.core.read .rsp).toNat ≤ (u.m.core.read .rbx).toNat)
    (hdgd : ∀ j < 32, ¬ StoredR (u.m.core.read .rbp) ((u.m.core.read .rbx).toNat + j))
    {name : List Byte} (hname : CStr u.m.memory (u.m.core.read .r12) name)
    (hnr : ∀ c ∈ name, c ∉ rejectBytes)
    (hnk : ∀ j < name.length + 1, W.Kept ((u.m.core.read .r12).toNat + j))
    (hnp : ∀ j < name.length + 1, ¬ E.S.priv u.m.memory ((u.m.core.read .r12).toNat + j))
    {st : St} (hst : StdoutIs E u.m.memory st)
    (k : ∀ w st', Body W (ShaMemP b lb sc) s0 w fr n saved → w.m.core.rip = b + 0x2c8a#64 →
      w.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], w.m.core.read r = u.m.core.read r) →
      StdoutIs E w.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      w.g.out ++ st'.buf = u.g.out ++ st.buf ++ (hexOf dg ++ [0x20#8, 0x20#8] ++ name ++ [0x0a#8]) →
      w.g.jobs = u.g.jobs → w.g.atexit = u.g.atexit → w.g.done = none →
      (w.g.inp = u.g.inp ∧ w.g.allocs = u.g.allocs ∧ w.g.heap = u.g.heap ∧
        w.g.files = u.g.files) → w.g.err = u.g.err →
      Keeps (fun a => W.Kept a ∨ ((u.m.core.read .rsp).toNat ≤ a ∧ ¬ StoredR (u.m.core.read .rbp) a))
        u.m.memory w.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file u.m.memory f st'' → E.S.file w.m.memory f st'') →
      LibK E W u.m.memory w.m.memory → MustQ W Q w) :
    MustQ W Q u := by
  have hroom := hB.room
  have hr1 := hroom.1
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by omega)
  set P := u.m.core.read .rbp with hPd
  set R := (u.m.core.read .rsp).toNat with hR
  have ad0 : (P + BitVec.signExtend 64 0xffffff30#32).toNat = P.toNat - 0xd0 := add_neg_toNat off_d0 (by omega) (by decide)
  have ac8 : (P + BitVec.signExtend 64 0xffffff38#32).toNat = P.toNat - 0xc8 := add_neg_toNat off_c8 (by omega) (by decide)
  have af8 : (P + BitVec.signExtend 64 0xffffff08#32).toNat = P.toNat - 0xf8 := add_neg_toNat off_f8 (by omega) (by decide)
  have aec : (P + BitVec.signExtend 64 0xffffff14#32).toNat = P.toNat - 0xec := add_neg_toNat off_ec (by omega) (by decide)
  refine sha_lineHead I hB hrip hlo hfr hn hsv hal hdelim hlen hslot hslot2 htag hname hnr hnk hnp ?_
  intro w hBw hwr hws hwc hw13 hwf hwg hs1 hs2 hkw hLw
  have tw : ∀ (a : Word) (j : Nat), R ≤ a.toNat → (∀ i < j, ¬ StoredR P (a.toNat + i)) →
      loadN w.m.memory a j = loadN u.m.memory a j := fun a j h1 h2 =>
    hkw.loadN (fun i hi => Or.inr ⟨by omega, h2 i hi⟩)
  have hwp : w.m.core.read .rbp = P := hwc .rbp (by simp)
  have hwb : w.m.core.read .rbx = u.m.core.read .rbx := hwc .rbx (by simp)
  have hstw : StdoutIs E w.m.memory st := ⟨hwf _ _ hst.1, hst.2⟩
  -- the hex digits
  have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by have := I.hb; omega)
  refine sha_hexLoop I hlo (by omega) hn hsv hal hrel (dg := dg) 32 0 w rfl (by decide) hBw hwr
    (by rw [loadN_keeps hkw (fun j hj => Or.inl (Or.inl (show W.InImage _ by
      rw [I.img, e78]; exact ⟨by omega, by omega⟩)))]; exact hlen) hw13
    (by rw [hwc .r14 (by simp), hr14]) (by rw [hwb, hkw.readBytes (fun j hj => Or.inr ⟨by omega, hdgd j hj⟩)]; exact hdg)
    (by rw [hws, hwb]; exact hdgs) st hstw ?_
  intro x st1 hBx hxr hxs hxc hst1 he1 hrd1 hef1 hg1 ho1 hj1 ha1 hd1 hi1 hie1 hkx hfx hLx
  have hxp : x.m.core.read .rbp = P := by rw [hxc .rbp (by simp), hwp]
  have hxs' : x.m.core.read .rsp = u.m.core.read .rsp := by rw [hxs, hws]
  have tx : ∀ (a : Word) (j : Nat), R ≤ a.toNat → loadN x.m.memory a j = loadN w.m.memory a j :=
    fun a j h1 => hkx.loadN (fun i hi => Or.inr (by rw [hws]; omega))
  have h12 : x.m.core.read .r12 = u.m.core.read .r12 := by rw [hxc .r12 (by simp), hwc .r12 (by simp)]
  have hkux : Keeps (fun a => W.Kept a ∨ (R ≤ a ∧ ¬ StoredR P a)) u.m.memory x.m.memory :=
    hkw.trans (hkx.mono fun a ha => by rw [hws]; rcases ha with h | h; exact Or.inl h; exact Or.inr h.1)
  refine sha_lineTail I hP hD hBx hxr hlo hfr hn hsv hal hrel (hv.keep (hkux.mono fun a ha => Or.inl ha)) hfk hfw
    (by rw [hxs', hxp]; exact hslot)
    (by rw [hxp, tx _ _ (by rw [ad0]; omega), tw _ _ (by rw [ad0]; omega)
      (fun i hi => by unfold StoredR; rw [ad0]; omega)]; exact htag)
    (by rw [hxp, tx _ _ (by rw [ac8]; omega), tw _ _ (by rw [ac8]; omega)
      (fun i hi => by unfold StoredR; rw [ac8]; omega)]; exact hbin) hbv
    (by rw [hxp, tx _ _ (by rw [af8]; omega)]; exact hs1)
    (by rw [hxp, tx _ _ (by rw [aec]; omega)]; exact hs2)
    ⟨hname.1, by rw [h12, hkux.readBytes (fun j hj => Or.inl (hnk j hj))]; exact hname.2⟩
    (by rw [h12]; exact hnk) hst1 ?_
  intro y st2 hBy hyr hys hyc hst2 he2 hrd2 hef2 hg2 ho2 hj2 ha2 hd2 hi2 hie2 hky hfy hLy
  have e0a : ((0x0a#64 : Word).setWidth 8) = 0x0a#8 := by decide
  refine k y st2 hBy hyr (by rw [hys, hxs']) (fun r hr => ?_) hst2 (by rw [he2, he1]) (by rw [hrd2, hrd1])
    (by rw [hef2, hef1]) (by rw [hg2, hg1]) ?_ (by rw [hj2, hj1, hwg]) (by rw [ha2, ha1, hwg]) hd2 ⟨by rw [hi2.1, hi1.1, hwg], by rw [hi2.2.1, hi1.2.1, hwg], by rw [hi2.2.2.1, hi1.2.2.1, hwg], by rw [hi2.2.2.2, hi1.2.2.2, hwg]⟩ (by rw [hie2, hie1, hwg])
    (hkux.trans (hky.mono fun a ha => by rw [hxs']; rcases ha with h | h; exact Or.inl h; exact Or.inr h.1))
    (fun f s'' hne hf => hfy f s'' hne (hfx f s'' hne (hwf f s'' hf))) (hLw.trans (hLx.trans hLy))
  · have hcs : r ∈ Silmaril.X86.sysv64.calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Silmaril.X86.sysv64_calleeSaved]
    rw [hyc r hcs, hxc r hr, hwc r hr]
  · rw [ho2, ho1, hwg, e0a]; simp [hexOf]

end Silmaril.Elf.Link.Dyn.Sha256sum
