module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestHead
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestEpi
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseIn

/-! # GNU `sha256sum`: `digest_file` on a named file, end to end (`Task.digestFile`)

From `0x6b50` the stream is closed with `rpl_fclose` (`0x6cb0`) and the function returns 1
(`dg_epi`). `task_digestFile` composes the pieces: prologue (`sha_digest_pro`), frame set-up
(`sha_digest_mid`), open and allocate (`sha_digest_head`), `SHA256_Init` (`dg_init`), the read
loop (`dg_loop`), the last block (`dg_flush`), `SHA256_Final` and `free` (`dg_final`), close and
return (`dg_tail_file`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

theorem ghost_eq {a c : Ghost} (h1 : a.jobs = c.jobs) (h2 : a.out = c.out) (h3 : a.atexit = c.atexit)
    (h4 : a.done = c.done) (h5 : a.inp = c.inp) (h6 : a.err = c.err)
    (h7 : a.allocs = c.allocs ∧ a.heap = c.heap ∧ a.files = c.files) (h10 : a.blocks = c.blocks) : a = c := by
  obtain ⟨h7, h8, h9⟩ := h7
  cases a; cases c; simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file`'s end on a named file** (`0x6b50`): `rpl_fclose (F)`, return 1. -/
theorem dg_tail_file {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {Q : PState → Prop} {s x : PState} {F g : Word} {z : BitVec 32} {d : Silmaril.Apps.Sha256sum.Bytes} {st : St}
    (hF : DigFin E W b lb kb (fun a => MX s a ∨ BR s a) s x F g z (ofSpec d) st) (hrip : x.m.core.rip = b + 0x6b50#64)
    (hz : z ≠ 0#32) (hfd : 3 ≤ st.fd) (habi : AbiEntry s.m.core s.m.memory)
    (hguard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hXo : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hnew : ∀ st0, ¬ E.S.file s.m.memory F st0)
    (k : ∀ t, DigExit E W s t d → MustQ W Q t) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hF.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := hF.lo
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.cl.img I.cl.hb
  have hX : ∀ a, (MX s a ∨ BR s a) → a + 1024 < (s.m.core.read .rsp).toNat ∨
      (s.m.core.read .rsp).toNat + 8 ≤ a := fun a h => Or.inr (hXo a h).2
  have hne : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
      (andD (BitVec.setWidth 32 (x.m.core.read .r14)) (BitVec.setWidth 32 (x.m.core.read .r14)))) .ne = some true := by
    rw [eval_ne_testD, hF.r14]; simp [hz]
  refine must_listed (o := 272) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 275) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 278) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hne]
  -- rpl_fclose (F), an internal call
  have hxr : (x.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have hx8 : (x.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hxr]; omega
  have pw : x.m.memory.Permitted .write (x.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have pr : x.m.memory.Permitted .read (x.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hpush : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat - 216 ≤ a) x.m.memory
      (pushMem x.m.memory (x.m.core.read .rsp) (b + 27829#64)) := by
    refine pushMem_keeps fun a ha => ?_
    rw [hx8]
    rcases ha with ha | ha
    · by_contra hc
      exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
    · omega
  have hroom1 : Room W (pushMem x.m.memory (x.m.core.read .rsp) (b + 27829#64)) (x.m.core.read .rsp - 8#64) 256 := by
    rw [show x.m.core.read .rsp - 8#64 = s.m.core.read .rsp - BitVec.ofNat 64 224 by rw [hB.rsp]; bv_omega]
    exact (hroom.pushMem.down (d := 224) (by decide) (by decide)).mono (by decide)
  have hf1 : E.S.file (pushMem x.m.memory (x.m.core.read .rsp) (b + 27829#64)) F st :=
    file_push hF.file (by rw [hx8]; omega)
  refine must_listed (o := 624) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using pw)]
  xstep []
  refine sha_rplFclose_in I.cl I.lseek (st := st) rfl
    (abiEntry_of (v := b + 27829#64) (by show (x.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hx8]; have := hF.al; omega)
      (by simpa using pushMem_read pr pw))
    (by simpa using hroom1) (by show E.S.lo + 256 ≤ (x.m.core.read .rsp - 8#64).toNat; rw [hx8]; omega) hB.done
    (hMk _ _ hB.mem (hpush.mono fun a ha => Or.inl (Or.inl ha))).1 (by simpa [hF.rbx] using hf1)
    hF.stok.2.2.1 hF.stok.2.1 hfd hF.stok.2.2.2.1 ?_
  intro t habiT hkT hoT hjT haT hdT hiT heT hcT hzT hokT hfsT hPT hLT
  have hLt : LibK E W s.m.memory t.m.memory :=
    (hF.lib.push (v := b + 27829#64) (by rw [hx8]; omega)).trans hLT
  obtain ⟨hB1, hrip1, hrsp1, hcs1⟩ := body_after (shaMemCD_keep I.cl.img I.cl.hb) hB (by decide) (by decide)
    (sv6_bound s) (ret := b + 27829#64)
    (hpost := ⟨⟨habiT, hkT.mono fun a ha => ha.1⟩, halfOfKeep hkT hPT, hdT⟩)
    (hem := by exact rfl) (hersp := by simp)
    (hecs := by
      intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (hefs := by exact rfl) (hvfs := hfsT) (hfp := fun x (h : False) => h.elim) (hX := fun x hd => hX x hd)
  have hkx : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat - 216 ≤ a) x.m.memory t.m.memory :=
    hpush.trans (hkT.mono fun a ha => by
      rcases ha with h | h
      · exact Or.inl h
      · right; show (x.m.core.read .rsp - 8#64).toNat ≤ a; rw [hx8]; omega)
  have hzT' : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
      (andD (BitVec.setWidth 32 (t.m.core.read .rax)) (BitVec.setWidth 32 (t.m.core.read .rax)))) .e = some true := by
    rw [eval_e_testD]; simp [show BitVec.setWidth 32 (t.m.core.read .rax) = 0#32 from hzT]
  refine must_listed (o := 629) shaD_listing_ok.2.2 rfl hB1.done (by rw [hrip1]; exact hin _ (by decide))
    hB1.mem.2.digestFile (by rw [hrip1, ripadd]) ?_
  xstep [hrip1]
  refine must_listed (o := 631) shaD_listing_ok.2.2 rfl hB1.done (hin _ (by decide)) hB1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hzT']
  refine must_gen (fun u => BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) (fun a => MX s a ∨ BR s a) ∧
      u.m.core.rip = b + 0x6b61#64 ∧ u.m.memory = t.m.memory ∧ u.g = t.g ∧
      u.m.core.read .rbp = s.m.core.read .rsp - 8#64) ?_ ?_
  · refine ⟨hB1.of_eq rfl (by simp) rfl rfl, by simp, rfl, rfl, ?_⟩
    simp only [st_read_mk, st_regs_apply]
    rw [hcs1 .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]
    simp [hF.rbp]
  rintro u ⟨hBu, hru, hmu, hgu, hbpu⟩
  refine dg_epi I.cl hBu hru hbpu (by rw [hmu, hkx.readBytes (fun j hj => Or.inr (by omega))]; exact hF.sg)
    habi hguard hgk hX (fun j hj hx => (hXo _ hx).1 (hgk j hj)) ?_
  intro t2 habi2 hm2 hax2 hg2 hfs2
  have hgt : t.g = { s.g with blocks := t.g.blocks } := by
    rw [← hF.g]
    exact ghost_eq (by rw [hjT]) (by rw [hoT]) (by rw [haT]) (by simp [hdT, hF.body.done]) (by rw [hiT]) (by rw [heT])
      (by rw [hcT.1, hcT.2.1, hcT.2.2]; exact ⟨rfl, rfl, rfl⟩) rfl
  refine k t2 ⟨habi2, by rw [hm2]; exact hBu.keepX, ?_, ?_, hax2, by rw [hg2, hgu, hgt], ?_, hfs2,
    by rw [hm2]; exact hBu.perm, by rw [hm2, hmu]; exact hF.pdx.keep hkx fun a _ ha => Or.inr (by omega),
    by rw [hm2, hmu]; exact hLt⟩
  · rw [hm2, hmu, hkx.readBytes (fun j hj => Or.inr (by have := (hXo _ (Or.inr ⟨le_refl _, by omega⟩)).2; omega))]
    exact hF.bin
  · rw [hm2, hmu, hkx.readBytes (fun j hj => Or.inr (by have := (hXo _ (Or.inl ⟨le_refl _, by omega⟩)).2; omega))]
    exact hF.miss
  · intro f st0 h
    have hne : f ≠ F := fun he => hnew st0 (he ▸ h)
    rw [hm2, hmu]
    exact hokT f st0 (by simpa [hF.rbx] using hne)
      (by simpa using file_push (v := b + 27829#64) (hF.others f st0 hne h) (by rw [hx8]; omega))

/-- **`digest_file` on a readable file** (`Task.digestFile`): proved. -/
theorem task_digestFile {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} : Task.digestFile E R W b lb kb := by
  intro I Q s p data g hE k
  obtain ⟨c0, hc0⟩ : ∃ c0, s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [c0] := by
    have h := Memory.readBytes_sub_range hE.name.2 (offset := 0) (len := 1) (by omega) (by omega)
    simp only [Nat.add_zero, List.drop_zero] at h
    cases p with
    | nil => exact ⟨0, by simpa using h⟩
    | cons c cs => exact ⟨c, by simpa using h⟩
  refine sha_digest_pro I.cl hE.rip hE.room hE.done hE.mem (fun u hP => ?_)
  refine sha_digest_mid I hP hE.lo hE.namek hc0 (hE.notDash c0 hc0) hE.outs hE.missw hE.missr hE.guard hE.guardk
    (fun x hM hrx h14 => ?_)
  refine sha_digest_head I hM hrx h14 hE.lo hE.abi.aligned hE.name hE.namek hE.file hE.outs hE.res
    (fun u F buf fd hP hru hfd3 hnew => ?_)
  refine dg_init I hP hru (fun v hv hrv => ?_)
  refine dg_loop I hv hrv (by simp) (fun v a p' st' hv' hrv' hrd herr hfd => ?_)
  refine dg_flush I hv' hrv' hrd (fun v2 hd hr2 => ?_)
  refine dg_final I hd hr2 ?_ hE.binw hE.binr (fun v3 hf hr3 => ?_)
  · intro a ha
    have h := hE.outs a (Or.inr ha)
    have hd := hE.disj
    unfold BR at ha
    dsimp only at ha ⊢
    exact ⟨fun hm => by unfold MX at hm; omega, h.1, h.2, fun hm => by omega⟩
  · exact dg_tail_file (s := { s with g := s.g.opened.alloc 0x8048 }) I hf hr3 h14 (by rw [hfd]; exact hfd3)
      hE.abi hE.guard hE.guardk hE.outs hnew k

end Silmaril.Elf.Link.Dyn.Sha256sum
