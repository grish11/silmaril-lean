module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteExitB
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteIter

/-! # GNU `sha256sum`: `Task.quoteExit`

From the loop head with the whole (plain) name copied into `slot0` (`QLoop` at `p.length`): the
NUL ends the loop, `buffer[len] = 0`, `quotearg_buffer_restyled` returns `len`,
`quotearg_n_options` restores `errno` and returns `slot0`, `quotef` returns: `QExit`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams

theorem ofSpec_toSpec (p : List Byte) : ofSpec (toSpec p) = p := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [ofSpec, toSpec, List.map_cons] at ih ⊢; rw [ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Task.quoteExit`**. -/
theorem task_quoteExit {E : Env} {W : World} {b lb : Word} : Task.quoteExit E W b lb := by
  intro Q s w p g ev hE hpl hL kX
  have hfit : p.length < 256 := by
    have := hE.fits
    rwa [FilesSpec.quotef_plain _ (by simpa [toSpec] using hpl.1) hpl.2, toSpec, List.length_map] at this
  have hn0 : 0 < p.length := List.length_pos_iff.2 hpl.1
  have hroom := hE.room
  have h4 : 2048 ≤ (s.m.core.read .rsp).toNat := hroom.1
  have hb := hE.imps.hb
  have I := hE.imps.img
  have hF := hL.F
  have hS := hL.stk
  have hd : w.g.done = none := by rw [hL.gh]; exact hE.done
  set R := s.m.core.read .rsp with hR
  set n := p.length with hn
  have hRR : R.toNat = (s.m.core.read .rsp).toNat := by rw [hR]
  have hRw : Room W w.m.memory R 2048 := hF.room hroom
  have hro : ShaRO b lb w.m.memory := QF.shaRO hE hF
  have hQC : ∀ {cb : Nat} {code : List Byte}, 0x2000 ≤ cb →
      cb + code.length ≤ 0x2000 + 0x4d51 → 0 < code.length → plainOk shaFile shaTextPh shaSlots cb code = true →
      QC W b w.m.memory cb code := fun h1 h2 h3 h4 => hro.qc I hb h1 h2 h3 h4
  have l0 : quoteX0Text.length = 496 := by decide
  have l4 : quoteX4Text.length = 23 := by decide
  have l5 : quoteX5Text.length = 129 := by decide
  have l6 : quoteX6Text.length = 326 := by decide
  have l7 : quoteX7Text.length = 393 := by decide
  have C0 : QC W b w.m.memory 0x4f50 quoteX0Text := hQC (by omega) (by omega) (by omega) quoteX0_plain
  have C4 : QC W b w.m.memory 0x5f99 quoteX4Text := hQC (by omega) (by omega) (by omega) quoteX4_plain
  have C5 : QC W b w.m.memory 0x6220 quoteX5Text := hQC (by omega) (by omega) (by omega) quoteX5_plain
  have C6 : QC W b w.m.memory 0x6614 quoteX6Text := hQC (by omega) (by omega) (by omega) quoteX6_plain
  have C7 : QC W b w.m.memory 0x681c quoteX7Text := hQC (by omega) (by omega) (by omega) quoteX7_plain
  -- the NUL after the name
  have hname := hE.name.2
  have hbound := permitted_bound (Memory.readWith_permitted hname)
  have hnb : s.m.memory.readBytes ((s.m.core.read .rdi).toNat + n) 1 = some [0#8] := by
    rw [Memory.readBytes_sub_range hname (offset := n) (len := 1)
      (by omega)
      (by omega),
      List.drop_append_of_le_length (by omega)]
    simp [hn]
  have hnbM : w.m.memory.readBytes ((s.m.core.read .rdi).toNat + n) 1 = some [0#8] := by
    rw [(hF.keepK hroom).readBytes (fun j hj => by
      have := hE.namek (n + j) (by omega); rwa [← Nat.add_assoc] at this)]; exact hnb
  have ha : (s.m.core.read .rdi + BitVec.ofNat 64 n).toNat = (s.m.core.read .rdi).toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hc8 : loadN w.m.memory (s.m.core.read .rdi + w.m.core.read .rbx) 1 = some 0#64 := by
    rw [hL.rbx]; simp [loadN, ha, hnbM, Silmaril.X86.Ext.leValue]
  -- 0x50c0
  refine qi_50c0 (v := w) hd (hro.qiCode I hb) hL.rip hL.r14 fun v1 S1 h1rip => ?_
  obtain ⟨S1m, S1g, S1fs, S1r⟩ := S1
  have hd1 : v1.g.done = none := by rw [S1g]; exact hd
  -- 0x50cd
  refine qx50cd (c := v1) (R := R) hd1 (by rw [S1m]; exact C0) h1rip
    (by rw [S1r _ (by decide), hL.rbp]) (nm := s.m.core.read .rdi) (by rw [S1m]; exact hS.f148)
    (by rw [S1m, S1r _ (by decide)]; exact hc8) fun c2 h2rip h2r10 h2o h2fs => ?_
  -- 0x50d9
  refine qx50d9 (c := ⟨⟨c2, _⟩, _⟩) hd1 (by rw [S1m]; exact C0) h2rip h2r10 fun c3 h3rip h3o h3fs => ?_
  have r3 : ∀ r, r ≠ .rax → r ≠ .r10 → c3.read r = w.m.core.read r := fun r a1 a2 => by
    rw [h3o r]; show c2.read r = _; rw [h2o r a1 a2, S1r r (by simp [a2])]
  have hLn : loadN w.m.memory (R - 0x130#64) 8 = some (BitVec.ofNat 64 n) := hL.len
  have hn64 : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  -- 0x5f99, 0x5faa
  refine qx5f99 (c := ⟨⟨c3, _⟩, _⟩) (R := R) hd1 (by rw [S1m]; exact C4) h3rip
    (by show c3.read .rbp = _; rw [r3 _ (by decide) (by decide), hL.rbp])
    (by rw [S1m]; exact hS.f134) (by rw [S1m]; exact hLn) hn64 fun c4 h4rip h4f h4o h4fs => ?_
  refine qx5faa (c := ⟨⟨c4, _⟩, _⟩) hd1 (by rw [S1m]; exact C4) h4rip h4f fun c5 h5rip h5o h5fs => ?_
  have r5 : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → c5.read r = w.m.core.read r := fun r a1 a2 a3 => by
    rw [h5o r]; show c4.read r = _; rw [h4o r a1 a2]; exact r3 r a1 a3
  -- 0x6220 .. 0x6270
  refine qx6220 (c := ⟨⟨c5, _⟩, _⟩) (R := R) hd1 (by rw [S1m]; exact C5) h5rip
    (by show c5.read .rbp = _; rw [r5 _ (by decide) (by decide) (by decide), hL.rbp])
    (by rw [S1m]; exact hS.f135) fun c6 h6rip h6f h6ax h6o h6fs => ?_
  refine qx6229 (c := ⟨⟨c6, _⟩, _⟩) hd1 (by rw [S1m]; exact C5) h6rip h6f fun c7 h7rip h7o h7fs => ?_
  have hq : b + 0x70d7#64 ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h
    rw [addr_toNat (by omega)] at this; simp at this
  refine qx622b (c := ⟨⟨c7, _⟩, _⟩) (R := R) hd1 (by rw [S1m]; exact C5) h7rip
    (by show c7.read .rbp = _; rw [h7o, h6o _ (by decide) (by decide), r5 _ (by decide) (by decide) (by decide),
      hL.rbp])
    (by rw [S1m]; exact hLn) (by rw [S1m]; exact hS.f190) hq fun c8 h8rip h8rdi h8r10 h8r11 h8o h8fs => ?_
  have r8 : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .rbx → r ≠ .rdi → r ≠ .r11 →
      c8.read r = w.m.core.read r := fun r a1 a2 a3 a4 a5 a6 => by
    rw [h8o r a4 a5 a3 a6]; show c7.read r = _; rw [h7o r]; show c6.read r = _
    rw [h6o r a1 a2]; exact r5 r a1 a2 a3
  have h8rdi' : c8.read .rdi = 256#64 := by
    rw [h8rdi]; show c7.read .r11 = _; rw [h7o, h6o _ (by decide) (by decide),
      r5 _ (by decide) (by decide) (by decide), hL.r11]
  have h8r10' : c8.read .r10 = b + 0xa060#64 := by
    rw [h8r10]; show c7.read .r9 = _; rw [h7o, h6o _ (by decide) (by decide),
      r5 _ (by decide) (by decide) (by decide), hL.r9]
  refine qx6241 (c := ⟨⟨c8, _⟩, _⟩) hd1 (by rw [S1m]; exact C5) h8rip
    (by show c8.read .rax = _; rw [h8o _ (by decide) (by decide) (by decide) (by decide)]; show c7.read .rax = _
        rw [h7o]; exact h6ax) fun c9 h9rip h9o h9fs => ?_
  refine qx6270 (c := ⟨⟨c9, _⟩, _⟩) hd1 (by rw [S1m]; exact C5) h9rip
    (by show (c9.read .r11).toNat < (c9.read .rdi).toNat
        rw [h9o, h9o, h8r11, h8rdi', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simpa using hfit)
    fun c10 h10rip h10o h10fs => ?_
  -- 0x6614
  have hSn : (b + 0xa060#64 + BitVec.ofNat 64 n).toNat = b.toNat + 0xa060 + n := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hSl : Slot0 b (b.toNat + 0xa060 + n) := by unfold Slot0; omega
  have hSk : W.Kept (b.toNat + 0xa060 + n) := Or.inl (by rw [I]; unfold ShaImg; omega)
  have hspw : ∀ x, R.toNat - 2048 ≤ x → x < R.toNat + 8 → x ≠ b.toNat + 0xa060 + n := fun x h1 h2 hx =>
    (hroom.2.2 x h1 h2).2.2 (by rw [hx]; exact hSk)
  have hs0 := hE.slot0 _ hSl
  have hperm := hF.perm _ hs0.2.2 hs0.1
  have hw0 : w.m.memory.Permitted .write (b + 0xa060#64 + BitVec.ofNat 64 n).toNat 1 :=
    qi_perm_of (by rw [hSn]; omega) fun j hj => by
      rw [hSn, show j = 0 by omega, Nat.add_zero, hperm]; exact hs0.2.1
  refine qx6614 (c := ⟨⟨c10, _⟩, _⟩) hd1 (by rw [S1m]; exact C6) h10rip (L := BitVec.ofNat 64 n)
    (by rw [h10o, h9o]; exact h8r10') (by rw [h10o, h9o]; exact h8r11) (by rw [S1m]; exact hw0)
    fun c11 h11rip h11o h11fs => ?_
  rw [S1m]
  set M1 := storeMem w.m.memory (b + 0xa060#64 + BitVec.ofNat 64 n) 1 0#64 with hM1
  have hK1 : Keeps (fun x => x ≠ b.toNat + 0xa060 + n) w.m.memory M1 :=
    storeMem_keeps fun x hx => by rw [hSn]; omega
  have hst : ∀ {d k : Nat}, d ≤ 2048 → k ≤ d + 8 → loadN M1 (R - BitVec.ofNat 64 d) k =
      loadN w.m.memory (R - BitVec.ofNat 64 d) k := fun hd hk =>
    hK1.loadN fun j hj => hspw _ (by rw [bsub_toNat (by omega)]; omega) (by rw [bsub_toNat (by omega)]; omega)
  have hfs11 : c11.fsBase = s.m.core.fsBase := by
    rw [h11fs]; show c10.fsBase = _; rw [h10fs]; show c9.fsBase = _; rw [h9fs]; show c8.fsBase = _
    rw [h8fs]; show c7.fsBase = _; rw [h7fs]; show c6.fsBase = _; rw [h6fs]; show c5.fsBase = _
    rw [h5fs]; show c4.fsBase = _; rw [h4fs]; show c3.fsBase = _; rw [h3fs]; show c2.fsBase = _
    rw [h2fs, S1fs, hL.fs]
  have hgM : loadN w.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g := by
    rw [(hF.keepK hroom).loadN fun j hj => ⟨hE.guardk j hj, hE.guardq j hj⟩]; exact hL.guard
  have hg1 : loadN M1 (s.m.core.fsBase + 0x28#64) 8 = some g := by
    rw [hK1.loadN fun j hj heq => hE.guardq j hj (by rw [heq]; exact hSl)]; exact hgM
  have r11 : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .rbx → r ≠ .rdi → r ≠ .r11 →
      c11.read r = w.m.core.read r := fun r a1 a2 a3 a4 a5 a6 => by
    rw [h11o]; show c10.read r = _; rw [h10o]; show c9.read r = _; rw [h9o]; exact r8 r a1 a2 a3 a4 a5 a6
  have hF1 : QF E W b s M1 := hF.local (fun a ha => ⟨(hE.slot0 a ha).2.2, (hE.slot0 a ha).1⟩) hE.lo
    (hK1.mono fun x hx heq => hx (Or.inl (by rw [heq]; exact hSl)))
    (hK1.mono fun x hx heq => by
      have hc := hL.ecell.2.2 (x - E.errnoA.toNat) (by unfold ErrnoR at hx; omega)
      apply hc
      rw [show E.errnoA.toNat + (x - E.errnoA.toNat) = x by unfold ErrnoR at hx; omega, heq, I]
      unfold ShaImg; omega) rfl
  have hro1 : ShaRO b lb M1 := QF.shaRO hE hF1
  have D5 : QC W b M1 0x6220 quoteX5Text := hro1.qc I hb (by omega) (by omega) (by omega) quoteX5_plain
  have D6 : QC W b M1 0x681c quoteX7Text := hro1.qc I hb (by omega) (by omega) (by omega) quoteX7_plain
  -- 0x6279
  refine qx6279 (c := ⟨⟨c11, M1⟩, _⟩) (R := R) hd1 D5 h11rip
    (by show c11.read .rbp = _; rw [r11 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hL.rbp]) (by show loadN M1 _ _ = _; rw [hst (by omega) (by omega)]; exact hS.f110)
    (by show loadN M1 (c11.fsBase + _) _ = _; rw [hfs11]; exact hg1) fun c12 h12rip h12o h12fs => ?_
  have r12' : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → r ≠ .rbx → r ≠ .rdi → r ≠ .r11 →
      c12.read r = w.m.core.read r := fun r a1 a2 a3 a4 a5 a6 => by
    rw [h12o r a1]; exact r11 r a1 a2 a3 a4 a5 a6
  have h12r11 : c12.read .r11 = BitVec.ofNat 64 n := by
    rw [h12o _ (by decide), h11o]; show c10.read .r11 = _; rw [h10o]; show c9.read .r11 = _; rw [h9o]; exact h8r11
  -- 0x628c
  refine qx628c (c := ⟨⟨c12, M1⟩, _⟩) (R := R) (ea := E.errnoA) hd1 D5 h12rip
    (by show c12.read .rsp = _; rw [r12' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hL.rsp])
    (by rw [hst (by omega) (by omega)]; exact hS.f100) (by rw [hst (by omega) (by omega)]; exact hS.ff8)
    (by rw [hst (by omega) (by omega)]; exact hS.ff0) (by rw [hst (by omega) (by omega)]; exact hS.fe8)
    (by rw [hst (by omega) (by omega)]; exact hS.fe0) (by rw [hst (by omega) (by omega)]; exact hS.fd8)
    (by rw [hst (by omega) (by omega)]; exact hS.fd0)
    fun c13 h13rip h13rsp h13rbp h13rbx h13r12 h13r13 h13r14 h13r15 h13rax h13fs => ?_
  -- 0x6859
  refine qx6859 (c := ⟨⟨c13, M1⟩, _⟩) (R := R) hd1 D6 h13rip h13rsp
    (by rw [hst (by omega) (by omega)]; exact hS.fc8) (by rw [hst (by omega) (by omega)]; exact hS.fc0)
    (by show (c13.read .rax).toNat < (c13.read .r14).toNat
        rw [h13rax, h13r14]; show (c12.read .r11).toNat < _
        rw [h12r11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega)
    fun c14 h14rip h14rsp h14o h14fs => ?_
  -- 0x68c7
  have hev4 : loadN w.m.memory (R - 0x94#64) 4 =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (Silmaril.X86.Ext.leBytes ev 4))) := by
    unfold loadN; rw [hS.f94]; rfl
  have hea1 : loadN M1 E.errnoA 4 = some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (Silmaril.X86.Ext.leBytes ev 4))) := by
    have hsi : W.InImage (b.toNat + 0xa060 + n) := by rw [I]; unfold ShaImg; omega
    rw [hK1.loadN fun j hj heq => hL.ecell.2.2 j hj (heq ▸ hsi),
      hF.errno.loadN fun j hj => ⟨by omega, by omega⟩]
    unfold loadN; rw [hL.ebytes]; rfl
  have hea : E.errnoA.toNat + 4 + 2048 ≤ R.toNat := by have := hE.errnoLo; have := hE.lo; omega
  refine qx68c7 (c := ⟨⟨c14, M1⟩, _⟩) (R := R) hd1 D6 h14rip
    (by show c14.read .rbp = _; rw [h14o _ (by decide) (by decide) (by decide)]; exact h13rbp)
    (by show c14.read .rbx = _; rw [h14o _ (by decide) (by decide) (by decide)]; exact h13rbx)
    (by rw [hst (by omega) (by omega)]; exact hev4) (readBytes_of_loadN' hea1 (by omega))
    ((hF1.errno.permitted fun j hj => ⟨by omega, by omega⟩).2 hL.ecell.2.1) hea
    (by rw [hst (by omega) (by omega)]; exact hS.f80) (by rw [hst (by omega) (by omega)]; exact hS.f78)
    (by rw [hst (by omega) (by omega)]; exact hS.f70) (by rw [hst (by omega) (by omega)]; exact hS.f68)
    (by rw [hst (by omega) (by omega)]; exact hS.f60) (by rw [hst (by omega) (by omega)]; exact hS.f58)
    (by rw [hst (by omega) (by omega)]; exact hS.f50)
    fun c15 h15rip h15rsp h15rbp h15rbx h15r12 h15r13 h15r14 h15r15 h15rax h15fs => ?_
  set M2 := storeMem M1 E.errnoA 4 (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (Silmaril.X86.Ext.leBytes ev 4)))
    with hM2
  have hS2 : Keeps (fun _ => True) M1 M2 := storeMem_same (readBytes_of_loadN' hea1 (by omega))
  have hF2 : QF E W b s M2 := hF1.local (fun a ha => ⟨(hE.slot0 a ha).2.2, (hE.slot0 a ha).1⟩) hE.lo
    (hS2.mono fun _ _ => trivial) (hS2.mono fun _ _ => trivial) rfl
  have hro2 : ShaRO b lb M2 := QF.shaRO hE hF2
  have E7 : QC W b M2 0x681c quoteX7Text := hro2.qc I hb (by omega) (by omega) (by omega) quoteX7_plain
  have hfs15 : c15.fsBase = s.m.core.fsBase := by
    rw [h15fs]; show c14.fsBase = _; rw [h14fs]; show c13.fsBase = _; rw [h13fs]; show c12.fsBase = _
    rw [h12fs]; exact hfs11
  -- 0x6994
  refine qx6994 (c := ⟨⟨c15, M2⟩, _⟩) (R := R) hd1 E7 h15rip h15rbp
    (by rw [hS2.loadN fun _ _ => trivial, hst (by omega) (by omega)]; exact hS.f10)
    (by show loadN M2 (c15.fsBase + _) _ = _; rw [hfs15, hS2.loadN fun _ _ => trivial]; exact hg1)
    fun c16 h16rip h16o h16fs => ?_
  -- 0x69a3
  have hra : loadN M2 R 8 = some (Silmaril.X86.FnContract.retOf s.m.core s.m.memory) := by
    rw [hS2.loadN fun _ _ => trivial, hK1.loadN fun j hj => hspw _ (by omega) (by omega)]
    rw [hF.keepC.loadN fun j hj => ⟨Or.inr (by omega), fun hq => by
      rcases hq with hq | hq
      · exact (hroom.2.2 (R.toNat + j) (by omega) (by omega)).2.2 (Or.inl (by rw [I]; unfold ShaImg Slot0 at *; omega))
      · omega⟩]
    exact loadN_of_enc hE.abi.returnAddress
  refine qx69a3 (c := ⟨⟨c16, M2⟩, _⟩) (R := R) hd1 E7 h16rip
    (by show c16.read .rbp = _; rw [h16o _ (by decide)]; exact h15rbp)
    (by rw [hS2.loadN fun _ _ => trivial, hst (by omega) (by omega)]; exact hS.f8) hra
    fun c17 h17rip h17rsp h17rbp h17o h17fs => ?_
  have hfs17 : c17.fsBase = s.m.core.fsBase := by
    rw [h17fs]; show c16.fsBase = _; rw [h16fs]; exact hfs15
  have r17 : ∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rdx → c17.read r = c15.read r := fun r a1 a2 a3 => by
    rw [h17o r a1 a2]; show c16.read r = _; rw [h16o r a3]
  -- QExit
  refine kX ⟨⟨c17, M2⟩, v1.g⟩ ⟨QF.final hF2 ⟨h17rip, h17rsp, ?_⟩ hfs17, S1g.trans hL.gh, hF2.others, ?_, ?_, ?_,
    hF2.slots hE, ?_⟩
  · intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    show c17.read r = _
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r17 _ (by decide) (by decide) (by decide)]; exact h15rbx
    · exact h17rbp
    · rw [r17 _ (by decide) (by decide) (by decide)]; exact h15r12
    · rw [r17 _ (by decide) (by decide) (by decide)]; exact h15r13
    · rw [r17 _ (by decide) (by decide) (by decide)]; exact h15r14
    · rw [r17 _ (by decide) (by decide) (by decide)]; exact h15r15
  · intro e he
    exact ⟨by rw [hF2.errno.loadN fun j hj => ⟨by omega, by omega⟩]; exact he.1,
      (hF2.errno.permitted fun j hj => ⟨by omega, by omega⟩).2 he.2⟩
  · show c17.read .rax = _
    rw [r17 _ (by decide) (by decide) (by decide), h15rax]
    show c14.read .r13 = _
    rw [h14o _ (by decide) (by decide) (by decide)]; exact h13r13
  · rw [FilesSpec.quotef_plain _ (by simpa [toSpec] using hpl.1) hpl.2, ofSpec_toSpec]
    refine ⟨hE.name.1, ?_⟩
    show M2.readBytes _ _ = _
    have hB0 : (b + 0xa060#64).toNat = b.toNat + 0xa060 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [hS2.readBytes fun _ _ => trivial]
    refine Silmaril.Process.Memory.readBytes_append ?_ ?_
    · rw [hK1.readBytes fun j hj => by rw [hB0]; omega]
      have := hL.pre
      rwa [List.take_of_length_le (by omega)] at this
    · have hr0 : w.m.memory.Permitted .read (b + 0xa060#64 + BitVec.ofNat 64 n).toNat 1 :=
        qi_perm_of (by rw [hSn]; omega) fun j hj => by
          rw [hSn, show j = 0 by omega, Nat.add_zero, hperm]; exact hs0.1
      have := storeMem_read (v := 0#64) hr0
      rw [hSn] at this
      rw [hB0]
      rw [this]; rfl
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := hE.slot0 a ha
    refine ⟨by rw [hF2.perm a h3 h1]; exact h1, by rw [hF2.perm a h3 h1]; exact h2, fun hp => ?_⟩
    rcases hF2.priv a hp with h | h
    · exact h3 h
    · rw [h1] at h; cases h

end Silmaril.Elf.Link.Dyn.Sha256sum
