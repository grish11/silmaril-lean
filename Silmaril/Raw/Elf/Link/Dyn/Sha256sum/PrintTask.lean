module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintLine
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinTasks
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainSpn

/-! # sha256sum's result line in `main`'s frame

`task_printLine`: `sha_printLine` instantiated at `main`'s frame (`PrintEntry` → `PrintExit`),
discharging `Task.printLine`.
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

theorem loadN_of_read {m : Memory} {a : Word} {k : Nat} {l : List Byte} (h : m.readBytes a.toNat k = some l) :
    loadN m a k = some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue l)) := by
  simp [loadN, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The result line, as `main` uses it** (`Task.printLine`). -/
theorem task_printLine {E : Env} {W : World} {b lb sc : Word} : Task.printLine E W b lb sc := by
  intro I hP hD Q s1 u sp dg name st he k
  have hlo := he.lo
  have hal := he.al
  have hs8 : (sp - 8#64).toNat = sp.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  have hur : (u.m.core.read .rsp).toNat = sp.toNat - 328 := by
    rw [he.body.rsp, he.hsp]; exact sub_toNat (by omega) (by decide)
  have hrbp : (u.m.core.read .rbp).toNat = sp.toNat - 8 := by rw [he.rbp, hs8]
  have hrbx : (u.m.core.read .rbx).toNat = sp.toNat - 104 := by
    rw [he.rbx, sub_toNat (k := 0x60) (by rw [hs8]; omega) (by decide), hs8]; omega
  have hb8 : (sp - 8#64 - 0x60#64).toNat = sp.toNat - 104 := by
    rw [sub_toNat (k := 0x60) (by rw [hs8]; omega) (by decide), hs8]; omega
  have at0 := add_neg_toNat (r := u.m.core.read .rbp) off_d0 (by omega) (by decide)
  have at8 := add_neg_toNat (r := u.m.core.read .rbp) off_c8 (by omega) (by decide)
  have e0 : BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [0#8]) = 0#64 := by decide
  have ea : BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [0x0a#8]) = 0x0a#64 := by decide
  have htag : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff30#32) 1 = some 0#64 := by
    rw [loadN_of_read (k := 1) (l := [0#8]) (by
      rw [at0, hrbp, show sp.toNat - 8 - 208 = sp.toNat - 216 by omega]; exact he.tag), e0]
  have hbin : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 4 =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue [0xff#8, 0xff#8, 0xff#8, 0xff#8])) :=
    loadN_of_read (by rw [at8, hrbp, show sp.toNat - 8 - 200 = sp.toNat - 208 by omega]; exact he.binary)
  refine sha_printLine I hP hD he.body he.rip (by rw [he.hsp]; omega) (by omega) (by decide)
    (sv6_bound328 s1) (by rw [he.hsp]; omega) he.rel he.vars he.footK he.fw
    (by rw [loadN_of_read he.delim, ea]) he.hexLen (by omega) (by rw [he.hsp]; omega) htag hbin
    (Or.inr (by decide)) he.r14 (by rw [hrbx, ← hb8]; exact he.hdg) (by omega)
    (fun j hj => by unfold StoredR; rw [hrbp, hrbx]; omega) he.hname
    (fun c hc => by
      have := he.noEsc c hc
      simp only [rejectBytes, List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h)
      · exact this.1 h
      · exact this.2.1 h
      · exact this.2.2 h)
    he.namek he.namep he.stdout ?_
  intro w st' hBw hwr hws hwc hst' herr hrd heof hrdg hout hj ha hdn hi hie hkw hfw hLw
  refine k w ⟨hBw, hwr, hws, hwc, ⟨st', hst', by rw [herr, he.stdoutErr], hrd, heof, hrdg, by simpa using hout⟩,
    ⟨hj, ha, hdn, hi⟩, hkw.mono fun a ha => ?_, hfw, hie, hLw⟩
  obtain ⟨h1 | h1, h2, h3⟩ := ha
  · exact Or.inl h1
  · right; refine ⟨by omega, ?_⟩
    unfold StoredR; rw [hrbp]; omega

end Silmaril.Elf.Link.Dyn.Sha256sum
