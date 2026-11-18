module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestFull

/-! # GNU `sha256sum`: the read loop of `digest_file` (`sha256_stream` inlined)

```
0x6b27: if (feof (stream)) goto done;            // test byte [rbx], 0x10
0x6ae8: n = fread (buffer + sum, 1, BLOCKSIZE - sum, stream); sum += n;
        if (sum == BLOCKSIZE) { SHA256_Update (ctx, buffer, BLOCKSIZE); sum = 0; continue; }
        if (n == 0) { if (ferror (stream)) error; goto done; }
done:   if (sum > 0) SHA256_Update (ctx, buffer, sum);
```
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- At the loop head with end of file seen: to `done` (`0x6b2c`). -/
theorem dg_head_eof {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s u : PState} {F buf g : Word} {z : BitVec 32}
    {data absorbed pending : List Byte} {st : St}
    (hI : DigInv E R W b lb kb X s u F buf g z data absorbed pending st) (hrip : u.m.core.rip = b + 0x6b27#64)
    (he : st.eof = true)
    (k : ∀ v, DigInv E R W b lb kb X s v F buf g z data absorbed pending st → v.m.core.rip = b + 0x6b2c#64 →
      MustQ W Q v) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hI.body
  obtain ⟨fl, hfl, hfl4, -, -⟩ := E.S.flags1 _ _ _ hI.file
  have hz : decide ((fl.setWidth 8 &&& BitVec.ofNat 8 (2 ^ 4)) = 0#8) = false := by
    rw [decide_eq_false_iff_not, testbit_and (by decide), hfl4, he]; decide
  refine must_listed (o := 231) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  rw [exec_testI8m _ _ _ _ _ fl (by rw [hI.rbx]; exact hfl), WP_ok]
  refine must_listed (o := 234) shaD_listing_ok.2.2 rfl hB.done (by simp only [hrip, ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [hrip, ripadd]) ?_
  xstep [eval_testFlags8 fl _ .e (Or.inl rfl), show (0x10#8 : BitVec 8) = BitVec.ofNat 8 (2 ^ 4) from rfl, hz, hrip]
  exact k _ (hI.congr rfl rfl rfl rfl) (by simp)

theorem readSt_app (st : St) (k : Nat) : (readSt st k).1 ++ (readSt st k).2.rd = st.rd := by
  simp only [readSt]; split
  · exact List.take_append_drop _ _
  · next h =>
    simp only [List.append_nil]
    exact List.take_of_length_le (by rw [List.length_take] at h; omega)

theorem readSt_fd (st : St) (k : Nat) : (readSt st k).2.fd = st.fd := by
  simp only [readSt]; split <;> rfl

theorem readSt_stok {st : St} {k : Nat}
    (h : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧ (st.eof = true → st.rd = [])) :
    (readSt st k).2.fail = false ∧ (readSt st k).2.err = false ∧ (readSt st k).2.reading = true ∧
      (readSt st k).2.fd < 2 ^ 31 ∧ ((readSt st k).2.eof = true → (readSt st k).2.rd = []) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [readSt]; split
  · refine ⟨h1, h2, h3, h4, fun he => ?_⟩
    simp only [h5 he, List.drop_nil]
  · exact ⟨h1, by simp [h1, h2], h3, h4, fun _ => rfl⟩

theorem readSt_short {st : St} {k : Nat} (hf : st.fail = false) :
    (readSt st k).1.length < k → (readSt st k).2.rd = [] ∧ (readSt st k).2.eof = true := by
  simp only [readSt]; split
  · next h => intro h'; simp only at h'; omega
  · intro _; simp [hf]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **One read of the loop** (end of file not yet seen). -/
theorem dg_iter {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s u : PState} {F buf g : Word} {z : BitVec 32}
    {data absorbed pending : List Byte} {st : St}
    (hI : DigInv E R W b lb kb X s u F buf g z data absorbed pending st) (hrip : u.m.core.rip = b + 0x6b27#64)
    (he : st.eof = false) (hk : pending.length < 0x8000)
    (kHead : ∀ v absorbed' pending' st', DigInv E R W b lb kb X s v F buf g z data absorbed' pending' st' →
      v.m.core.rip = b + 0x6b27#64 → pending'.length < 0x8000 →
      st'.rd.length + (if st'.eof then 0 else 1) < st.rd.length + 1 → st'.fd = st.fd → MustQ W Q v)
    (kExit : ∀ v pending' st', DigInv E R W b lb kb X s v F buf g z data absorbed pending' st' →
      v.m.core.rip = b + 0x6b2c#64 → st'.rd = [] → st'.err = false → st'.fd = st.fd → MustQ W Q v) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hI.body
  obtain ⟨fl, hfl, hfl4, -, -⟩ := E.S.flags1 _ _ _ hI.file
  have hz : decide ((fl.setWidth 8 &&& BitVec.ofNat 8 (2 ^ 4)) = 0#8) = true := by
    rw [decide_eq_true_eq, testbit_and (by decide), hfl4, he]
  refine must_listed (o := 231) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  rw [exec_testI8m _ _ _ _ _ fl (by rw [hI.rbx]; exact hfl), WP_ok]
  refine must_listed (o := 234) shaD_listing_ok.2.2 rfl hB.done (by simp only [hrip, ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [hrip, ripadd]) ?_
  xstep [eval_testFlags8 fl _ .e (Or.inl rfl), show (0x10#8 : BitVec 8) = BitVec.ofNat 8 (2 ^ 4) from rfl, hz, hrip]
  refine must_listed (o := 168) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 173) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 176) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 180) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 183) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 186) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 189) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  have hk64 : (BitVec.ofNat 64 pending.length).toNat = pending.length := Nat.mod_eq_of_lt (by omega)
  have hae : Silmaril.X86.Ext.Cond.afterCmp (w := 63) (u.m.core.read .r15) 32840#64 .ae = false := by
    simp only [Silmaril.X86.Ext.Cond.afterCmp, hI.r15, BitVec.ult, hk64, Bool.not_eq_false']
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  refine must_listed (o := 194) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [eval_cmpQ, eval_cmp64, hae]
  refine must_listed (o := 198) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  -- the call of __fread_unlocked_chk (buf + k, BLOCKSIZE + 72 - k, 1, BLOCKSIZE - k, F)
  refine must_gen (fun v => BodyX W (ShaMemCD b lb kb) s v 216 1024 (sv6 s) X ∧ v.m.core.rip = b + 0x6b09#64 ∧
      v.m.memory = u.m.memory ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧ v.g = u.g ∧
      v.m.core.read .rdi = buf + BitVec.ofNat 64 pending.length ∧
      v.m.core.read .rsi = 32840#64 - BitVec.ofNat 64 pending.length ∧ v.m.core.read .rdx = 1#64 ∧
      v.m.core.read .rcx = 0x8000#64 - BitVec.ofNat 64 pending.length ∧ v.m.core.read .r8 = F ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨hB.of_eq rfl (by simp) rfl rfl, rfl, rfl, by simp, rfl, by simp [hI.r12, hI.r15], by simp [hI.r15],
      by simp, by simp [hI.r13, hI.r15], by simp [hI.rbx], ?_⟩
    intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro v ⟨hBv, hrv, hmv, hspv, hgv, hdiv, hsiv, hdxv, hcxv, hr8v, hcsv⟩
  have hsv := sv6_bound s
  have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by have := hI.al; have := hI.lo; omega
  have hbb := permitted_bound hI.bufr
  have hkn : (buf + BitVec.ofNat 64 pending.length).toNat = buf.toNat + pending.length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show pending.length < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hnn : (0x8000#64 - BitVec.ofNat 64 pending.length).toNat = 0x8000 - pending.length := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega
  have hsn : (32840#64 - BitVec.ofNat 64 pending.length).toNat = 32840 - pending.length := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega
  have hv8 : (v.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hBv.rsp]; exact sub_toNat (by have := hI.lo; omega) (by decide)
  have hprivv : ∀ m', (∀ a, a < E.S.lo → m'.bytes.get? a = v.m.memory.bytes.get? a ∧
      ∀ acc, m'.permits acc a = v.m.memory.permits acc a) → E.S.priv m' = E.S.priv v.m.memory :=
    fun m' h => E.S.priv_local _ _ h
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hBv (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 201) (so := 0x310) (pb := b + 0x23c0#64)
    (fp := fun a => (buf + BitVec.ofNat 64 pending.length).toNat ≤ a ∧
      a < (buf + BitVec.ofNat 64 pending.length).toNat + (readSt st (1 * (0x8000 - pending.length))).1.length)
    shaD_listing_ok.2.2 rfl (by rw [hrv]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hrv, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x310 + 4 + 6) + BitVec.signExtend 64 0x7886#32 = b + 0x9f60#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.freadChk)
    I.fread.1 I.fread.2.1 I.fread.2.2.1 (fun r h => contract_cond ((impOk_fn I.fread _ r).1 h))
    ?_ ?_ ?_ ?_ ?_
  · intro he
    have hlo8 : E.S.lo ≤ (v.m.core.read .rsp - 8#64).toNat := by
      rw [sub_toNat (k := 8) (by have := hI.lo; omega) (by decide), hv8]; have := hI.lo; omega
    have hpp : E.S.priv (pushMem v.m.memory (v.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))) =
        E.S.priv u.m.memory := by
      rw [hprivv _ (fun a ha => ⟨(pushMem_keeps (P := fun x => x < E.S.lo) (m := v.m.memory) (sp := v.m.core.read .rsp)
        (v := b + 27200#64 + BitVec.ofNat 64 (201 + 5)) (fun x hx => Or.inl (by omega)) a ha).1, fun acc => rfl⟩), hmv]
    rw [callEntry_read _ _ _ (by decide : Reg.rdx ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.rcx ≠ .rsp),
      callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.r8 ≠ .rsp),
      callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdxv, hcxv, hsiv, hr8v, hdiv, callEntry_mem, hkn, hnn, hsn,
      show (1#64 : Word).toNat = 1 from rfl, Nat.one_mul, hpp]
    refine ⟨by omega, he, ⟨st, file_push (by rw [hmv]; exact hI.file) hlo8⟩,
      permitted_sub (by rw [pushMem_permitted, hmv]; exact hI.bufw) (by omega) (by omega) (by omega), by decide,
      permitted_sub (by rw [pushMem_permitted, hmv]; exact hI.bufr) (by omega) (by omega) (by omega),
      fun a h1 h2 => (hI.bufok a (by omega) (by omega)).2.2.2, ?_⟩
    simp only [callEntry_rsp]; exact hlo8
  · intro w hw
    have hlo8 : E.S.lo ≤ (v.m.core.read .rsp - 8#64).toNat := by
      rw [sub_toNat (k := 8) (by have := hI.lo; omega) (by decide), hv8]; have := hI.lo; omega
    have hf' : E.S.file (callEntry v (lb + 1274160#64) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).m.memory
        ((callEntry v (lb + 1274160#64) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).m.core.read .r8) st := by
      rw [callEntry_read _ _ _ (by decide : Reg.r8 ≠ .rsp), hr8v, callEntry_mem]
      exact file_push (by rw [hmv]; exact hI.file) hlo8
    have hw' := hw st hf'
    rw [callEntry_read _ _ _ (by decide : Reg.rdx ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.rcx ≠ .rsp),
      callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdxv, hcxv, hdiv, hnn,
      show (1#64 : Word).toNat = 1 from rfl] at hw'
    rcases hrs : readSt st (1 * (0x8000 - pending.length)) with ⟨d, st'⟩
    rw [hrs] at hw'
    obtain ⟨hlib, hgw, -, -, -, -⟩ := hw'
    refine ⟨?_, hlib.2.2.1, hlib.2.1, by rw [hgw]; exact hBv.done⟩
    simpa [hrs] using hlib.1
  · intro a ha
    simp only [readSt_fst, List.length_take, hkn] at ha
    have := hI.bufok a (by omega) (by omega)
    exact ⟨this.1, Or.inl (by omega)⟩
  · exact fun a h => hI.hX a h
  · intro w hw hBw hrw hspw hcsw hkw
    have hlo8 : E.S.lo ≤ (v.m.core.read .rsp - 8#64).toNat := by
      rw [sub_toNat (k := 8) (by have := hI.lo; omega) (by decide), hv8]; have := hI.lo; omega
    have hpe : ∀ a, a < E.S.lo → (pushMem v.m.memory (v.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).bytes.get? a
        = u.m.memory.bytes.get? a ∧ ∀ acc, (pushMem v.m.memory (v.m.core.read .rsp)
          (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).permits acc a = u.m.memory.permits acc a := by
      intro a ha
      rw [← hmv]
      exact ⟨(pushMem_keeps (P := fun x => x < E.S.lo) (m := v.m.memory) (sp := v.m.core.read .rsp)
        (v := b + 27200#64 + BitVec.ofNat 64 (201 + 5)) (fun x hx => Or.inl (by omega)) a ha).1, fun acc => rfl⟩
    have hpp : E.S.priv (pushMem v.m.memory (v.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))) =
        E.S.priv u.m.memory := E.S.priv_local _ _ hpe
    have hf' : E.S.file (callEntry v (lb + 1274160#64) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).m.memory
        ((callEntry v (lb + 1274160#64) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).m.core.read .r8) st := by
      rw [callEntry_read _ _ _ (by decide : Reg.r8 ≠ .rsp), hr8v, callEntry_mem]
      exact file_push (by rw [hmv]; exact hI.file) hlo8
    have hw' := hw st hf'
    rw [callEntry_read _ _ _ (by decide : Reg.rdx ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.rcx ≠ .rsp),
      callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdxv, hcxv, hdiv, hnn,
      show (1#64 : Word).toNat = 1 from rfl, Nat.one_mul] at hw'
    rcases hrs : readSt st (0x8000 - pending.length) with ⟨d, st'⟩
    rw [hrs] at hw'
    obtain ⟨hlib, hgw, hokw, hfw, hrdw, hraxw⟩ := hw'
    have hd : d = st.rd.take (0x8000 - pending.length) := by rw [← readSt_fst, hrs]
    have hdl : d.length ≤ 0x8000 - pending.length := by rw [hd, List.length_take]; omega
    have hLw : LibK E W s.m.memory w.m.memory := (hI.lib.of_eq hmv).call hlo8 hlib fun a ha hf => by
      simp only [hkn] at hf
      exact hI.buffr a (by omega) (by omega) ha
    obtain ⟨⟨-, hkr⟩, -, -, hkp, hpg, hperm, -⟩ := hlib
    simp only [callEntry_mem, hpp] at hkp hpg hperm
    -- the buffer
    have hbmapped : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → u.m.memory.permits .read a = true := by
      intro a h1 h2
      have := hI.bufr; unfold Memory.Permitted at this; rw [Memory.checkSpan_iff] at this
      have h := this.2.2 (a - buf.toNat) (by omega); rwa [show buf.toNat + (a - buf.toNat) = a by omega] at h
    have hpushp : ∀ a acc, (pushMem v.m.memory (v.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (201 + 5))).permits
        acc a = u.m.memory.permits acc a := fun a acc => by rw [← hmv]; rfl
    have hbk : Keeps (fun a => buf.toNat ≤ a ∧ a < buf.toNat + pending.length) u.m.memory w.m.memory := by
      intro a ha
      have hb := hI.bufok a ha.1 (by omega)
      have h1 := hkp a ⟨hb.2.2.2, fun hf => by simp only [hkn] at hf; omega, by rw [hpushp]; exact hbmapped a ha.1 (by omega)⟩
      refine ⟨?_, fun acc => ?_⟩
      · rw [h1.1, ← hmv]
        exact (pushMem_keeps (P := fun x => x < E.S.lo) (m := v.m.memory) (sp := v.m.core.read .rsp)
          (v := b + 27200#64 + BitVec.ofNat 64 (201 + 5)) (fun x hx => Or.inl (by omega)) a (by omega)).1
      · rw [h1.2 acc, hpushp]
    have hbuf : w.m.memory.readBytes buf.toNat (pending.length + d.length) = some (pending ++ d) :=
      Memory.readBytes_append (by rw [hbk.readBytes (fun j hj => ⟨by omega, by omega⟩)]; exact hI.bufrd)
        (by rw [← hkn]; exact hrdw)
    have hbperm : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → ∀ acc, w.m.memory.permits acc a = u.m.memory.permits acc a := by
      intro a h1 h2 acc
      rw [hperm a (hI.bufok a h1 h2).2.2.2 (by rw [hpushp]; exact hbmapped a h1 h2) acc, hpushp]
    have hbr : w.m.memory.Permitted .read buf.toNat 0x8048 := by
      have := hI.bufr; unfold Memory.Permitted at this ⊢; rw [Memory.checkSpan_iff] at this ⊢
      exact ⟨this.1, this.2.1, fun j hj => by rw [hbperm _ (by omega) (by omega)]; exact this.2.2 j hj⟩
    have hbw : w.m.memory.Permitted .write buf.toNat 0x8048 := by
      have := hI.bufw; unfold Memory.Permitted at this ⊢; rw [Memory.checkSpan_iff] at this ⊢
      exact ⟨this.1, this.2.1, fun j hj => by rw [hbperm _ (by omega) (by omega)]; exact this.2.2 j hj⟩
    have hbok : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 →
        ¬ W.Kept a ∧ a + 0x100000 < (s.m.core.read .rsp).toNat ∧ a < E.S.lo ∧ ¬ E.S.priv w.m.memory a := by
      intro a h1 h2
      have hb := hI.bufok a h1 h2
      refine ⟨hb.1, hb.2.1, hb.2.2.1, fun hp => ?_⟩
      rcases hpg a hp with h | h
      · exact hb.2.2.2 h
      · rw [hpushp, hbmapped a h1 h2] at h; cases h
    -- the frame
    have hkF : Keeps (fun a => (s.m.core.read .rsp).toNat - 216 ≤ a ∧ ¬ (buf.toNat ≤ a ∧ a < buf.toNat + 0x8048))
        u.m.memory w.m.memory := by
      rw [← hmv]
      refine hkw.mono fun a ha => ⟨Or.inr ha.1, fun hf => ha.2 ⟨by simp only [hkn, Nat.one_mul, hrs] at hf; omega, by
        simp only [hkn, Nat.one_mul, hrs] at hf; omega⟩⟩
    have hbelow : buf.toNat + 0x8048 ≤ (s.m.core.read .rsp).toNat - 1024 := by
      have := (hI.bufok (buf.toNat + 0x8047) (by omega) (by omega)).2.1; omega
    have hsl : ∀ o, o ≤ 216 → 8 ≤ o → w.m.memory.readBytes ((s.m.core.read .rsp).toNat - o) 8 =
        u.m.memory.readBytes ((s.m.core.read .rsp).toNat - o) 8 := fun o h1 h2 =>
      hkF.readBytes (fun j hj => ⟨by have := hI.lo; omega, by omega⟩)
    have hrdx := hI.rdxhi
    have hmiss : w.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8] := by
      rw [hkF.readBytes (fun j hj => ⟨by omega, by omega⟩)]
      exact hI.miss
    have hctx : ∀ j, j < 112 → (s.m.core.read .rsp).toNat - 216 ≤ (s.m.core.read .rsp - 184#64).toNat + j ∧
        ¬ (buf.toNat ≤ (s.m.core.read .rsp - 184#64).toNat + j ∧ (s.m.core.read .rsp - 184#64).toNat + j < buf.toNat + 0x8048) := by
      have : (s.m.core.read .rsp - 184#64).toNat = (s.m.core.read .rsp).toNat - 184 :=
        sub_toNat (k := 184) (by have := hI.lo; omega) (by decide)
      intro j hj; rw [this]; omega
    have hholds : R.holds w.m.memory (s.m.core.read .rsp - 184#64) absorbed :=
      R.local_ _ _ _ _ (hkF.mono fun a ha => hctx (a - (s.m.core.read .rsp - 184#64).toNat) (by omega)
        |> fun h => by rwa [show (s.m.core.read .rsp - 184#64).toNat + (a - (s.m.core.read .rsp - 184#64).toNat) = a by
          omega] at h) hI.holds
    have hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, w.m.core.read r = u.m.core.read r := fun r hr => by
      rw [hcsw r hr, hcsv r hr]
    have hgw' : w.g = u.g := by rw [hgw]; simp only [callEntry_g]; exact hgv
    have hothers : ∀ f st0, f ≠ F → E.S.file s.m.memory f st0 → E.S.file w.m.memory f st0 := fun f st0 hne h =>
      hokw f st0 (by rw [callEntry_read _ _ _ (by decide : Reg.r8 ≠ .rsp), hr8v]; simpa using hne)
        (by rw [callEntry_mem]; exact file_push (by rw [hmv]; exact hI.others f st0 hne h) hlo8)
    have hr15w : w.m.core.read .r15 = BitVec.ofNat 64 pending.length := by
      rw [hcs .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), hI.r15]
    have hsum : BitVec.ofNat 64 pending.length + BitVec.ofNat 64 d.length = BitVec.ofNat 64 (pending.length + d.length) := by
      rw [BitVec.ofNat_add]
    have hraxw' : w.m.core.read .rax = BitVec.ofNat 64 d.length := by rw [hraxw, Nat.div_one]
    refine must_listed (o := 206) shaD_listing_ok.2.2 rfl hBw.done (by rw [hrw]; exact img_off I.cl.img I.cl.hb (by decide))
      hBw.mem.2.digestFile (by rw [hrw, ripadd]) ?_
    xstep [hrw, hr15w, hraxw', hsum]
    refine must_gen (fun x => BodyX W (ShaMemCD b lb kb) s x 216 1024 (sv6 s) X ∧ x.m.core.rip = b + 0x6b11#64 ∧
        x.m.memory = w.m.memory ∧ x.g = w.g ∧ x.m.core.read .rax = BitVec.ofNat 64 d.length ∧
        x.m.core.read .r15 = BitVec.ofNat 64 (pending ++ d).length ∧
        (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r15 → x.m.core.read r = w.m.core.read r)) ?_ ?_
    · refine ⟨hBw.of_eq rfl (by simp) rfl rfl, by simp, rfl, rfl, by simp [hraxw'], by simp, ?_⟩
      intro r hr hne
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl hne | simp
    rintro x ⟨hBx, hrx, hmx, hgx, hrax, hr15x, hcsx⟩
    have hreg : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r15 → x.m.core.read r = u.m.core.read r :=
      fun r hr hne => by rw [hcsx r hr hne, hcs r hr]
    have hst := readSt_stok (k := 0x8000 - pending.length) hI.stok
    have happ := readSt_app st (0x8000 - pending.length)
    rw [hrs] at hst happ
    have hfx : E.S.file x.m.memory F st' := by
      rw [hmx]
      have := hfw; rwa [callEntry_read _ _ _ (by decide : Reg.r8 ≠ .rsp), hr8v] at this
    have hpdxw : PermDX s w.m.memory :=
      (show PermDX s v.m.memory by rw [hmv]; exact hI.pdx).keep hkw fun a _ ha =>
        ⟨Or.inr (by omega), fun hf => by simp only [hkn, Nat.one_mul, hrs] at hf; omega⟩
    have hIx : DigInv E R W b lb kb X s x F buf g z data absorbed (pending ++ d) st' :=
      ⟨hI.hX, hI.lo, hI.al, hBx, by rw [hreg .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.rbp,
        by rw [hreg .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.rbx,
        by rw [hreg .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.r12,
        by rw [hreg .r13 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.r13,
        by rw [hreg .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.r14,
        hr15x, by simp only [List.length_append]; omega,
        by rw [hmx, hsl 200 (by decide) (by decide)]; exact hI.sbin,
        by rw [hmx, hsl 192 (by decide) (by decide)]; exact hI.sctx,
        by rw [hmx, hsl 64 (by decide) (by decide)]; exact hI.sg,
        by rw [hmx]; exact hmiss, hI.rdxhi, by rw [hmx]; exact hholds,
        by rw [hmx, List.length_append]; exact hbuf, by rw [hmx]; exact hbr, by rw [hmx]; exact hbw,
        by rw [hmx]; exact hbok, hfx, hst, by rw [← hI.data, ← happ]; simp only [List.append_assoc],
        by rw [hgx, hgw']; exact hI.g, by rw [hmx]; exact hothers, by rw [hmx]; exact hpdxw,
        by rw [hmx]; exact hLw, hI.buffr⟩
    have hkpos : 0 < 0x8000 - pending.length := by omega
    have hfd' : st'.fd = st.fd := by
      have := readSt_fd st (0x8000 - pending.length); rw [hrs] at this; exact this
    refine dg_after I hIx hrx hrax (by omega) ?_ ?_ ?_
    · intro hfl v hv hrv
      have hdk : d.length = 0x8000 - pending.length := by simp only [List.length_append] at hfl; omega
      have hst' : st' = { st with rd := st.rd.drop (0x8000 - pending.length) } := by
        have hc : (st.rd.take (0x8000 - pending.length)).length = 0x8000 - pending.length := by rw [← hd]; exact hdk
        have h := hrs; simp only [readSt, hc, ↓reduceIte] at h
        exact (Prod.mk.inj h).2.symm
      have hrl : 0x8000 - pending.length ≤ st.rd.length := by
        have := congrArg List.length hd; rw [List.length_take] at this; omega
      refine kHead v _ [] st' hv hrv (by simp) ?_ hfd'
      rw [hst']; simp only [List.length_drop, he]; simp; omega
    · intro hfl hn v hv hrv
      have hsh := readSt_short (k := 0x8000 - pending.length) (st := st) hI.stok.1
      rw [hrs] at hsh; simp only at hsh
      obtain ⟨h1, h2⟩ := hsh (by simp only [List.length_append] at hfl; omega)
      refine kHead v _ _ st' hv hrv hfl ?_ hfd'
      rw [h1, h2]; simp
    · intro hfl hn v hv hrv
      have hsh := readSt_short (k := 0x8000 - pending.length) (st := st) hI.stok.1
      rw [hrs] at hsh; simp only at hsh
      obtain ⟨h1, -⟩ := hsh (by omega)
      exact kExit v _ st' hv hrv h1 hst.2.1 hfd'

/-- **The read loop of `digest_file`**: from the head (`0x6b27`) to `done` (`0x6b2c`) with the
whole input read, without a read error. -/
theorem dg_loop {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s u : PState} {F buf g : Word} {z : BitVec 32}
    {data absorbed pending : List Byte} {st : St}
    (hI : DigInv E R W b lb kb X s u F buf g z data absorbed pending st) (hrip : u.m.core.rip = b + 0x6b27#64)
    (hk : pending.length < 0x8000)
    (kExit : ∀ v absorbed' pending' st', DigInv E R W b lb kb X s v F buf g z data absorbed' pending' st' →
      v.m.core.rip = b + 0x6b2c#64 → st'.rd = [] → st'.err = false → st'.fd = st.fd → MustQ W Q v) :
    MustQ W Q u := by
  suffices H : ∀ N, ∀ u absorbed pending st', st'.rd.length + (if st'.eof = true then 0 else 1) < N →
      st'.fd = st.fd →
      DigInv E R W b lb kb X s u F buf g z data absorbed pending st' → u.m.core.rip = b + 0x6b27#64 →
      pending.length < 0x8000 → MustQ W Q u from
    H _ u absorbed pending st (Nat.lt_succ_self _) rfl hI hrip hk
  intro N
  induction N with
  | zero => intro u a p st' hN; omega
  | succ N ih =>
    intro u a p st' hN hfd hI hrip hk
    cases he : st'.eof
    · rw [he] at hN
      exact dg_iter I hI hrip he hk
        (fun v a' p' st'' hv hrv hp' hm hf => ih v a' p' st''
          (by simp only [Bool.false_eq_true, ↓reduceIte] at hN; omega) (hf.trans hfd) hv hrv hp')
        (fun v p' st'' hv hrv hrd herr hf => kExit v _ _ _ hv hrv hrd herr (hf.trans hfd))
    · exact dg_head_eof I hI hrip he (fun v hv hrv => kExit v _ _ _ hv hrv (hI.stok.2.2.2.2 he) hI.stok.2.1 hfd)

end Silmaril.Elf.Link.Dyn.Sha256sum
