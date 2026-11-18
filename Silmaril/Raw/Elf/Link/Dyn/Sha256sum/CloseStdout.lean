module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseStream

/-! # GNU `sha256sum`: `close_stdout` -/

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
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

theorem loadN_keeps {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {a : Word} {n : Nat}
    (hP : ∀ k < n, P (a.toNat + k)) : loadN m' a n = loadN m a n := by
  simp only [loadN, h.readBytes hP]

/-- The two libc variables `stdout` and `stderr` hold the streams' `FILE` pointers. -/
structure StdVars (E : Env) (W : World) (lb : Word) (m : Memory) : Prop where
  out : loadN m (lb + 0x2056a8#64) 8 = some E.stdoutF
  err : loadN m (lb + 0x2056a0#64) 8 = some E.stderrF
  kept : ∀ k < 16, W.Kept ((lb + 0x2056a0#64).toNat + k)
  bound : (lb + 0x2056a0#64).toNat + 16 ≤ 2 ^ 64

theorem StdVars.keep {E : Env} {W : World} {lb : Word} {m m' : Memory} (h : StdVars E W lb m)
    (hk : Keeps W.Kept m m') : StdVars E W lb m' := by
  have e : (lb + 0x2056a8#64).toNat = (lb + 0x2056a0#64).toNat + 8 := by
    have := h.bound
    rw [show lb + 0x2056a8#64 = lb + 0x2056a0#64 + 8#64 by rw [BitVec.add_assoc]; rfl, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by rw [show (8#64).toNat = 8 from rfl]; omega)]
    rfl
  refine ⟨?_, ?_, h.kept, h.bound⟩
  · rw [loadN_keeps hk (fun k hk => by rw [e, Nat.add_assoc]; exact h.kept _ (by omega))]; exact h.out
  · rw [loadN_keeps hk (fun k hk => h.kept k (by omega))]; exact h.err

theorem below32_a1 {x sp : Nat} (h1 : sp - 1024 ≤ x) : sp - 32 - 524288 ≤ x :=
  Nat.le_trans (Nat.le_trans (Nat.sub_le_sub_right (Nat.sub_le sp 32) _)
    (Nat.sub_le_sub_left (by decide : 1024 ≤ 524288) sp)) h1
theorem below32_a2 {x sp : Nat} (hx : ¬ sp - 32 ≤ x) : x < sp - 32 + 8 :=
  Nat.lt_of_lt_of_le (Nat.lt_of_not_le hx) (Nat.le_add_right _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`close_stdout`** (`0x69b0`, gnulib, run at exit): with `stdout` and `stderr` free of errors
and reliable writes, it writes `stdout`'s buffer out and returns. -/
theorem sha_closeStdout {E : Env} {W : World} {b lb : Word} (I : CloseImps E W b lb) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x69b0#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 1024) (hlo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat)
    (hd : s.g.done = none) (hm : ShaMemC b lb s.m.memory) (hrel : W.reliable = true)
    (hv : StdVars E W lb s.m.memory) (hne : E.stderrF ≠ E.stdoutF)
    {st1 st2 : St} (hf1 : E.S.file s.m.memory E.stdoutF st1) (hr1 : st1.reading = false)
    (he1 : st1.err = false) (hfd1 : st1.fd = 1)
    (hf2 : E.S.file s.m.memory E.stderrF st2) (hr2 : st2.reading = false)
    (he2 : st2.err = false) (hfd2 : st2.fd = 2)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory →
      t.g.out = s.g.out ++ st1.buf → t.g.jobs = s.g.jobs → t.g.atexit = s.g.atexit → t.g.done = none →
      t.g.inp = s.g.inp → t.g.err = s.g.err → MustQ W Q t) :
    MustQ W Q s := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hal := habi.aligned
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p2 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r2 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hk1 : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory
      (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) :=
    push_keeps_caller hroom (by omega) (by omega)
  have hk2 : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a)
      (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) (s.m.core.read .rsp - 8#64)
        (s.m.core.read .rbx)) :=
    push_keeps_caller hroom (by rw [e8]; omega) (by rw [e8]; omega)
  have hm2 := shaMemC_keep I.img I.hb _ _ hm ((hk1.trans hk2).mono fun x hx => Or.inl (Or.inl hx))
  have hm1 := shaMemC_keep I.img I.hb _ _ hm (hk1.mono fun x hx => Or.inl (Or.inl hx))
  have hv2 := hv.keep ((hk1.trans hk2).mono fun x hx => Or.inl hx)
  refine must_listed (o := 0) shaC_listing_ok.2.2.2 rfl hd (by rw [hrip]; exact hin _ (by decide)) hm.closeStdout
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hrip]
  refine must_listed (o := 4) shaC_listing_ok.2.2.2 rfl hd (hin _ (by decide)) hm.closeStdout (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 5) shaC_listing_ok.2.2.2 rfl hd (hin _ (by decide)) hm1.closeStdout (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) shaC_listing_ok.2.2.2 rfl hd (hin _ (by decide)) hm1.closeStdout (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p2)]
  xstep []
  refine must_listed (o := 9) shaC_listing_ok.2.2.2 rfl hd (hin _ (by decide)) hm2.closeStdout (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 24 1024 [(8, s.m.core.read .rbp), (16, s.m.core.read .rbx)] ∧
      u.m.core.rip = b + 0x69bd#64 ∧ u.m.core.read .rbp = s.m.core.read .rsp - 8#64 ∧
      (∀ r ∈ [Reg.r12, Reg.r13, Reg.r14, Reg.r15], u.m.core.read r = s.m.core.read r) ∧ u.g = s.g ∧
      StdVars E W lb u.m.memory ∧ (∀ f st', E.S.file s.m.memory f st' → E.S.file u.m.memory f st')) ?_ ?_
  · refine ⟨⟨?_, keepF (hk1.trans hk2), hroom.pushMem.pushMem, hm2, rfl, hd, ?_,
      fun a _ _ acc => by simp [pushMem_permits]⟩, rfl, by simp, ?_, rfl, hv2, ?_⟩
    · simp; bv_omega
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simp only
        rw [read_push_ne (by rw [e16, e8]; omega) (by rw [e8]; omega) (by rw [e8]; omega)]
        exact push_read_after r1 p1 e8
      · simp only
        rw [show (s.m.core.read .rsp).toNat - 16 = (s.m.core.read .rsp - 8#64).toNat - 8 by rw [e8]; omega]
        exact push_read_after (by simpa [pushMem_permitted] using r2) (by simpa [pushMem_permitted] using p2)
          (by rw [e16, e8]; omega)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    · intro f st' h
      exact file_push (file_push h (by rw [e8]; omega)) (by rw [e16]; omega)
  rintro u ⟨hB, hrip1, hrbp1, hcs1, hg1, hv1, hfk1⟩
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have hu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 32 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hur]; omega
  have pw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hB.room (Or.inr rfl) (by omega) (by omega)
  have pr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hB.room (Or.inl rfl) (by omega) (by omega)
  refine must_listed (o := 13) shaC_listing_ok.2.2.2 rfl hB.done (by rw [hrip1]; exact hin _ (by decide))
    hB.mem.closeStdout (by rw [hrip1, ripadd]) ?_
  xstep [hrip1, hB.mem.stdoutV]
  refine must_listed (o := 20) shaC_listing_ok.2.2.2 rfl hB.done (hin _ (by decide))
    hB.mem.closeStdout (by rw [ripadd]) ?_
  rw [exec_loadq _ _ _ _ _ _ (by exact hv1.out)]
  xstep []
  refine must_listed (o := 23) shaC_listing_ok.2.2.2 rfl hB.done (hin _ (by decide))
    hB.mem.closeStdout (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using pw)]
  xstep []
  have hsp32 : u.m.core.read .rsp - 8#64 = s.m.core.read .rsp - BitVec.ofNat 64 32 := by
    rw [hB.rsp]; bv_omega
  have hroom1 : Room W (pushMem u.m.memory (u.m.core.read .rsp) (b + 27084#64)) (u.m.core.read .rsp - 8#64) 512 := by
    rw [hsp32]; exact (hB.room.pushMem.down (d := 32) (by decide) (by decide)).mono (by decide)
  have hfo : E.S.file (pushMem u.m.memory (u.m.core.read .rsp) (b + 27084#64)) E.stdoutF st1 :=
    file_push (hfk1 _ _ hf1) (by rw [hu8]; omega)
  refine sha_closeStream_out I (st := st1) rfl
    (abiEntry_of (v := b + 27084#64) (by show (u.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hu8]; omega)
      (by simpa using pushMem_read pr pw))
    (by simpa using hroom1) (by show E.S.lo + 512 ≤ (u.m.core.read .rsp - 8#64).toNat; rw [hu8]; omega) hB.done
    (shaMemC_keep I.img I.hb _ _ hB.mem (room_push_img hB.room (by omega) (by omega))) hrel
    (by simpa using hfo) hr1 he1 (by omega) ?_
  intro t1 habi1 hkT1 ho1 hj1 ha1 hd1 hi1 he1' hz1 hO1 hP1
  have hrip_t1 : t1.m.core.rip = b + 27084#64 := by
    rw [habi1.pc]; exact retOf_of (by simpa using pushMem_read pr pw)
  have hrsp_t1 : t1.m.core.read .rsp = u.m.core.read .rsp := by rw [habi1.stack]; simp
  have hcs_t1 : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t1.m.core.read r = u.m.core.read r := by
    intro r hr
    rw [habi1.calleeSaved r hr]
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hkU1 : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat - 24 ≤ a) u.m.memory t1.m.memory := by
    refine (pushMem_keeps (fun x hx => ?_)).trans (hkT1.mono fun x hx => ?_)
    · rcases hx with hx | hx
      · by_cases hc : (s.m.core.read .rsp).toNat - 1024 ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8
        · exact absurd hx (hB.room.2.2 x hc.1 hc.2).2.2
        · rw [hu8]; omega
      · rw [hu8]; omega
    · rcases hx with hx | hx
      · exact Or.inl hx
      · right; show (u.m.core.read .rsp - 8#64).toNat ≤ x; rw [hu8]; omega
  have hmT1 : ShaMemC b lb t1.m.memory :=
    shaMemC_keep I.img I.hb _ _ hB.mem (hkU1.mono fun x hx => Or.inl (Or.inl hx))
  have hvT1 : StdVars E W lb t1.m.memory := hv1.keep (hkU1.mono fun x hx => Or.inl hx)
  have hz1' : BitVec.setWidth 32 (t1.m.core.read .rax) = 0#32 := hz1
  have hpermT1 : ∀ x, (s.m.core.read .rsp).toNat - 1024 ≤ x → x < (s.m.core.read .rsp).toNat + 8 →
      ∀ acc, t1.m.memory.permits acc x = u.m.memory.permits acc x := by
    intro x h1 h2 acc
    by_cases hx : (s.m.core.read .rsp).toNat - 32 ≤ x
    · rw [(hkT1 x (Or.inr (by show (u.m.core.read .rsp - 8#64).toNat ≤ x; rw [hu8]; exact hx))).2 acc]
      simp [pushMem_permits]
    · rw [hP1 x (by show (u.m.core.read .rsp - 8#64).toNat - 0x80000 ≤ x; rw [hu8]; exact below32_a1 h1)
        (by show x < (u.m.core.read .rsp - 8#64).toNat + 8; rw [hu8]; exact below32_a2 hx) acc]
      simp [pushMem_permits]
  have hroomT1 : Room W t1.m.memory (s.m.core.read .rsp) 1024 := hB.room.keeps hpermT1
  have hfe1 : E.S.file t1.m.memory E.stderrF st2 :=
    hO1 _ _ (by simpa using hne) (by simpa using file_push (v := b + 27084#64) (hfk1 _ _ hf2) (by rw [hu8]; omega))
  refine must_listed (o := 28) shaC_listing_ok.2.2.2 rfl hd1 (by rw [hrip_t1]; exact hin _ (by decide))
    hmT1.closeStdout (by rw [hrip_t1, ripadd]) ?_
  xstep [hrip_t1]
  refine must_listed (o := 30) shaC_listing_ok.2.2.2 rfl hd1 (hin _ (by decide)) hmT1.closeStdout (by rw [ripadd]) ?_
  xstep [eval_e_testD, hz1']
  refine must_listed (o := 96) shaC_listing_ok.2.2.2 rfl hd1 (hin _ (by decide)) hmT1.closeStdout (by rw [ripadd]) ?_
  xstep [hmT1.stderrV]
  refine must_listed (o := 103) shaC_listing_ok.2.2.2 rfl hd1 (hin _ (by decide)) hmT1.closeStdout (by rw [ripadd]) ?_
  rw [exec_loadq _ _ _ _ _ _ (by exact hvT1.err)]
  xstep []
  have pw2 : t1.m.memory.Permitted .write (t1.m.core.read .rsp - 8#64).toNat 8 := by
    rw [hrsp_t1]; exact room_perm hroomT1 (Or.inr rfl) (by rw [hu8]; omega) (by rw [hu8]; omega)
  have pr2 : t1.m.memory.Permitted .read (t1.m.core.read .rsp - 8#64).toNat 8 := by
    rw [hrsp_t1]; exact room_perm hroomT1 (Or.inl rfl) (by rw [hu8]; omega) (by rw [hu8]; omega)
  refine must_listed (o := 106) shaC_listing_ok.2.2.2 rfl hd1 (hin _ (by decide)) hmT1.closeStdout (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using pw2)]
  xstep []
  have hu8' : (t1.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 32 := by rw [hrsp_t1]; exact hu8
  have hroom2 : Room W (pushMem t1.m.memory (t1.m.core.read .rsp) (b + 27167#64)) (t1.m.core.read .rsp - 8#64) 512 := by
    rw [hrsp_t1, hsp32]; exact (hroomT1.pushMem.down (d := 32) (by decide) (by decide)).mono (by decide)
  refine sha_closeStream_out I (st := st2) rfl
    (abiEntry_of (v := b + 27167#64) (by show (t1.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hu8']; omega)
      (by simpa using pushMem_read pr2 pw2))
    (by simpa using hroom2) (by show E.S.lo + 512 ≤ (t1.m.core.read .rsp - 8#64).toNat; rw [hu8']; omega) hd1
    (shaMemC_keep I.img I.hb _ _ hmT1 (room_push_img hroomT1 (by rw [hrsp_t1]; omega) (by rw [hrsp_t1]; omega))) hrel
    (by simpa using file_push (v := b + 27167#64) hfe1 (by rw [hu8']; omega)) hr2 he2 (by omega) ?_
  intro t2 habi2 hkT2 ho2 hj2 ha2 hd2 hi2 he2' hz2 hO2 hP2
  have hrip_t2 : t2.m.core.rip = b + 27167#64 := by
    rw [habi2.pc]; exact retOf_of (by simpa using pushMem_read pr2 pw2)
  have hrsp_t2 : t2.m.core.read .rsp = u.m.core.read .rsp := by rw [habi2.stack]; simp [hrsp_t1]
  have hcs_t2 : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t2.m.core.read r = u.m.core.read r := by
    intro r hr
    rw [habi2.calleeSaved r hr]
    have hr' := hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hcs_t1 _ hr]
  have hkU2 : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat - 24 ≤ a) t1.m.memory t2.m.memory := by
    refine (pushMem_keeps (fun x hx => ?_)).trans (hkT2.mono fun x hx => ?_)
    · rcases hx with hx | hx
      · by_cases hc : (s.m.core.read .rsp).toNat - 1024 ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8
        · exact absurd hx (hroomT1.2.2 x hc.1 hc.2).2.2
        · rw [hu8']; omega
      · rw [hu8']; omega
    · rcases hx with hx | hx
      · exact Or.inl hx
      · right; show (t1.m.core.read .rsp - 8#64).toNat ≤ x; rw [hu8']; omega
  have hmT2 : ShaMemC b lb t2.m.memory :=
    shaMemC_keep I.img I.hb _ _ hmT1 (hkU2.mono fun x hx => Or.inl (Or.inl hx))
  have hz2' : BitVec.setWidth 32 (t2.m.core.read .rax) = 0#32 := hz2
  have hrbp2 : t2.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by
    rw [hcs_t2 .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbp1]
  have svb := hB.saved (16, s.m.core.read .rbx) (by simp)
  have svp := hB.saved (8, s.m.core.read .rbp) (by simp)
  simp only at svb svp
  rw [← (hkU1.trans hkU2).readBytes (fun j hj => Or.inr (by omega))] at svb svp
  have hret2 : t2.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [(hkU1.trans hkU2).readBytes (fun j hj => Or.inr (by omega)), (Body.keep hB).readBytes (fun j hj => Or.inr (by omega))]
    exact habi.returnAddress
  have hA16 : (s.m.core.read .rsp - 8#64 + BitVec.signExtend 64 0xfffffff8#32).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [show BitVec.signExtend 64 0xfffffff8#32 = 0xfffffffffffffff8#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  refine must_listed (o := 111) shaC_listing_ok.2.2.2 rfl hd2 (by rw [hrip_t2]; exact hin _ (by decide))
    hmT2.closeStdout (by rw [hrip_t2, ripadd]) ?_
  xstep [hrip_t2]
  refine must_listed (o := 113) shaC_listing_ok.2.2.2 rfl hd2 (hin _ (by decide)) hmT2.closeStdout (by rw [ripadd]) ?_
  xstep [eval_ne_testD, hz2']
  refine must_listed (o := 115) shaC_listing_ok.2.2.2 rfl hd2 (hin _ (by decide)) hmT2.closeStdout (by rw [ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN t2.m.memory (t2.m.core.read .rbp + BitVec.signExtend 64 0xfffffff8#32) 8 = _
    rw [hrbp2]; exact loadN_of_enc (by rw [hA16]; exact svb))]
  xstep []
  refine must_listed (o := 119) shaC_listing_ok.2.2.2 rfl hd2 (hin _ (by decide)) hmT2.closeStdout (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hrbp2, e8, svp]
  refine must_listed (o := 120) shaC_listing_ok.2.2.2 rfl hd2 (hin _ (by decide)) hmT2.closeStdout (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hret2]
  have hgu : u.g = s.g := hg1
  refine k _ ⟨rfl, by simp, ?_⟩ ?_ ?_ ?_ ?_ hd2 ?_ ?_
  · intro r hr
    have hr' := hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    all_goals simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true]; rw [st_regs_apply, hcs_t2 _ hr]; exact hcs1 _ (by simp)
  · exact (Body.keep hB).trans ((hkU1.trans hkU2).mono fun x hx => by
      rcases hx with h | h; exact Or.inl h; exact Or.inr (by omega))
  · rw [ho2, ho1]; simp [hfd1, hfd2, hgu]
  · rw [hj2, hj1]; simp [hgu]
  · rw [ha2, ha1]; simp [hgu]
  · rw [hi2, hi1]; simp [hgu]
  · rw [he2', he1']; simp [hgu]

end Silmaril.Elf.Link.Dyn.Sha256sum
