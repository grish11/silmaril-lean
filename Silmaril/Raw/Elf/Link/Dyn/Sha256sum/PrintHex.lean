module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintPut1

/-! # sha256sum's output path, part (b): the hex digits of the digest

`sha_hexStep`: one iteration of the loop at `0x2bc8` (`__printf_chk (2, "%02x", digest[i])`,
`i += 1`, `i < digest_hex_bytes / 2`); `sha_hexLoop`: all 32 iterations, appending
`hex2 digest[0] ++ … ++ hex2 digest[31]` to `stdout`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

/-- The bytes `0 … i-1` of `dg`, in hex. -/
def hexOf (dg : List Byte) : List Byte := dg.flatMap hex2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha_hexStep {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc)
    {Q : PState → Prop} {s0 v : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 v fr n saved) (hrip : v.m.core.rip = b + 0x2bc8#64)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    (hlen : loadN v.m.memory (b + 0xa178#64) 8 = some 64#64)
    {i : Nat} (hi : i < 32) (hr13 : v.m.core.read .r13 = BitVec.ofNat 64 i)
    (hr14 : v.m.core.read .r14 = b + 0x7238#64)
    {dg : List Byte} (hdg : v.m.memory.readBytes (v.m.core.read .rbx).toNat 32 = some dg)
    {st : St} (hst : StdoutIs E v.m.memory st)
    (k : ∀ w st', Body W (ShaMemP b lb sc) s0 w fr n saved →
      w.m.core.rip = (if i + 1 < 32 then b + 0x2bc8#64 else b + 0x2bef#64) →
      w.m.core.read .rsp = v.m.core.read .rsp →
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], w.m.core.read r = v.m.core.read r) →
      w.m.core.read .r13 = BitVec.ofNat 64 (i + 1) →
      StdoutIs E w.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      w.g.out ++ st'.buf = v.g.out ++ st.buf ++ hex2 (dg[i]'(by
        have := Silmaril.Process.Memory.readWith_length hdg; omega)) →
      w.g.jobs = v.g.jobs → w.g.atexit = v.g.atexit → w.g.done = none →
      (w.g.inp = v.g.inp ∧ w.g.allocs = v.g.allocs ∧ w.g.heap = v.g.heap ∧
        w.g.files = v.g.files) → w.g.err = v.g.err →
      Keeps (fun a => W.Kept a ∨ (v.m.core.read .rsp).toNat ≤ a) v.m.memory w.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file v.m.memory f st'' → E.S.file w.m.memory f st'') →
      LibK E W v.m.memory w.m.memory → MustQ W Q w) :
    MustQ W Q v := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  have hdl : dg.length = 32 := Silmaril.Process.Memory.readWith_length hdg
  obtain ⟨hra, hrw, -⟩ := Streams.Total.perm_of_read hdg
  have hbyte : loadN v.m.memory (v.m.core.read .rbx + v.m.core.read .r13) 1 =
      some (BitVec.ofNat 64 (dg[i]'(by omega)).toNat) := by
    have hsub := Streams.Total.sub_read hdg (k := i) (j := 1) (by omega) (by omega)
    have ha : (v.m.core.read .rbx + BitVec.ofNat 64 i).toNat = (v.m.core.read .rbx).toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [hr13]
    simp only [loadN, ha, hsub, Option.map_some]
    congr 2
    rw [List.take_one, List.drop_eq_getElem_cons (by omega)]
    simp [List.getElem?_eq_getElem (show i < dg.length by omega), Silmaril.X86.Ext.leValue]
  refine must_listed (o := 62) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_movzb_idx _ _ _ _ hbyte]
  simp only [WP_ok, ripadd, hrip]
  refine must_listed (o := 67) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 70) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 75) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN]
  refine must_listed (o := 77) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN]
  have hu : (v.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by have := hB.room.1; omega) (by have := hB.room.1; omega)
  have hroom1 := hB.room.1
  have hlo8 : E.S.lo ≤ (v.m.core.read .rsp - 8#64).toNat := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hu]; omega
  have hpush : ∀ x : Word, ShaMemP b lb sc (pushMem v.m.memory (v.m.core.read .rsp) x) := fun x =>
    shaMemP_keep I.img I.hb _ _ hB.mem (by
      rw [I.img]; exact img_push I.img hB.room (by rw [hu]; omega) (by rw [hu]; omega))
  refine must_gen (fun x => x.m.core.rip = b + 11227#64 ∧ x.m.core.read .rsi = b + 0x7238#64 ∧
      x.m.core.read .rdx = (dg[i]'(by omega)).setWidth 64 ∧ x.m.core.read .r13 = v.m.core.read .r13 + 1#64 ∧
      x.m.core.read .rsp = v.m.core.read .rsp ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], x.m.core.read r = v.m.core.read r) ∧
      x.m.memory = v.m.memory ∧ x.g = v.g ∧ x.m.core.fsBase = v.m.core.fsBase)
    ⟨rfl, by simp [hr14], by simp, by simp; rfl, by simp, fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  rintro x ⟨hxr, hxsi, hxdx, hx13, hxsp, hxc, hxm, hxg, hxf⟩
  have hBx : Body W (ShaMemP b lb sc) s0 x fr n saved := hB.of_eq hxm hxsp hxf (by rw [hxg])
  have hdx : x.g.done = none := hBx.done
  refine body_call (shaMemP_keep I.img I.hb) hBx hfr hn hsv hal I.lz
    (o := 81) (so := 0) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaP_listing_ok.1 rfl (by rw [hxr]; exact hin _ (by decide)) (fun m h => h.printLine) (by rw [hxr, ripadd])
    shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0 + 4 + 6) + BitVec.signExtend 64 0x7a0e#32 =
        b + 0x9dd8#64 by simp only [BitVec.add_assoc]; rfl]
      exact h.printfChk)
    I.printf.1 I.printf.2.1 I.printf.2.2.1 (fun r h => (impOk_fn I.printf _ r).1 h)
    (fun habi => ⟨habi, ⟨by decide, ?cs⟩, st, ?std⟩)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, hw.2.1.2.2.1⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  case cs =>
    rw [callEntry_mem, callEntry_read _ _ _ (by decide), hxsi, hxm, hxsp]
    exact (hpush _).fmtHex
  case std =>
    rw [callEntry_mem, hxm, hxsp]
    exact ⟨file_push hst.1 hlo8, hst.2⟩
  intro w hw hB2 hrip2 hrsp2 hcs2
  have hLw : LibK E W v.m.memory w.m.memory := ((LibK.refl E W _).of_eq hxm).call0 (by rw [hxsp]; exact hlo8) hw.1
  obtain ⟨⟨⟨-, hkw⟩, -⟩, ⟨hj, ha, hdn, hii, hie, hal, hhp, hfi⟩, hoth, happ⟩ := hw
  have hoth' : ∀ f st'', f ≠ E.stdoutF → E.S.file v.m.memory f st'' → E.S.file w.m.memory f st'' :=
    fun f st'' hne hf => hoth f st'' (by simpa using hne) (by rw [callEntry_mem, hxm, hxsp]; exact file_push hf hlo8)
  have hdw : w.g.done = none := hdn
  have hkv : Keeps (fun a => W.Kept a ∨ (v.m.core.read .rsp).toNat ≤ a) v.m.memory w.m.memory := by
    rw [← hxm]
    refine (pushMem_keeps fun y hy => ?_).trans (hkw.mono fun y hy => ⟨?_, id⟩)
    · rw [hxsp]
      rcases hy with h | h
      · by_cases hc : (s0.m.core.read .rsp).toNat - n ≤ y ∧ y < (s0.m.core.read .rsp).toNat + 8
        · exact absurd h (hB.room.2.2 y hc.1 hc.2).2.2
        · rw [sub_toNat (k := 8) (by omega) (by decide)]; omega
      · rw [sub_toNat (k := 8) (by omega) (by decide)]; omega
    · rcases hy with h | h
      · exact Or.inl h
      · right; rw [callEntry_rsp, hxsp, sub_toNat (k := 8) (by omega) (by decide)]; omega
  have hlenw : loadN w.m.memory (b + 0xa178#64) 8 = some 64#64 := by
    have e : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by have := I.hb; omega)
    rw [loadN_keeps hkv (fun j hj => Or.inl (Or.inl (show W.InImage _ by rw [I.img, e]; exact ⟨by omega, by omega⟩)))]
    exact hlen
  have hr13w : w.m.core.read .r13 = BitVec.ofNat 64 (i + 1) := by
    rw [hcs2 .r13 (by simp [Silmaril.X86.sysv64_calleeSaved]), hx13, hr13, BitVec.ofNat_add]
  refine must_listed (o := 86) shaP_listing_ok.1 rfl hdw (by rw [hrip2, ripadd]; exact hin _ (by decide))
    hB2.mem.printLine (by rw [hrip2, ripadd]) ?_
  xstep [hrip2, hlenw]
  refine must_listed (o := 93) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hB2.mem.printLine
    (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.ShiftOp.result]
  refine must_listed (o := 96) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hB2.mem.printLine
    (by rw [ripadd]) ?_
  xstep [hr13w, Silmaril.X86.Ext.AluOp.flagsN]
  refine must_listed (o := 99) shaP_listing_ok.1 rfl hdw (hin _ (by decide)) hB2.mem.printLine
    (by rw [ripadd]) ?_
  xstep [eval_b_sub, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
  -- what the call appended
  obtain ⟨st', hst', heof, hrd, hrdg, hor⟩ := happ st (by
    rw [callEntry_mem, hxm, hxsp]; exact ⟨file_push hst.1 hlo8, hst.2⟩)
  obtain ⟨hout, herr⟩ : w.g.out ++ st'.buf = v.g.out ++ st.buf ++ hex2 (dg[i]'(by omega)) ∧
      st'.err = st.err := by
    rcases hor with h | ⟨hr, -⟩
    · refine ⟨?_, h.2⟩
      rw [h.1, callEntry_g, hxg, callEntry_read _ _ _ (by decide), hxdx]
      simp
    · rw [hrel] at hr; cases hr
  have hmem : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], r ∈ Silmaril.X86.sysv64.calleeSaved := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Silmaril.X86.sysv64_calleeSaved]
  have hcw : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], w.m.core.read r = v.m.core.read r := by
    intro r hr
    rw [hcs2 r (hmem r hr)]
    exact hxc r hr
  by_cases hlt : i + 1 < 32
  · simp only [Nat.mod_eq_of_lt (show i + 1 < 18446744073709551616 by omega), hlt, decide_true, WP_ok]
    refine k _ st' (hB2.of_eq rfl (by simp) rfl rfl) (by simp [hlt]) (by simp [hrsp2, hxsp]) (fun r hr => ?_)
      (by simpa using hr13w) hst' herr hrd heof hrdg hout (by rw [hj, callEntry_g, hxg])
      (by rw [ha, callEntry_g, hxg]) hdw ⟨by rw [hii, callEntry_g, hxg], by rw [hal, callEntry_g, hxg], by rw [hhp, callEntry_g, hxg],
        by rw [hfi, callEntry_g, hxg]⟩ (by rw [hie, callEntry_g, hxg]) hkv hoth' hLw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simpa using hcw _ (by simp)
  · simp only [Nat.mod_eq_of_lt (show i + 1 < 18446744073709551616 by omega), hlt, decide_false, WP_ok]
    refine k _ st' (hB2.of_eq rfl (by simp) rfl rfl) (by simp [hlt]) (by simp [hrsp2, hxsp]) (fun r hr => ?_)
      (by simpa using hr13w) hst' herr hrd heof hrdg hout (by rw [hj, callEntry_g, hxg])
      (by rw [ha, callEntry_g, hxg]) hdw ⟨by rw [hii, callEntry_g, hxg], by rw [hal, callEntry_g, hxg], by rw [hhp, callEntry_g, hxg],
        by rw [hfi, callEntry_g, hxg]⟩ (by rw [hie, callEntry_g, hxg]) hkv hoth' hLw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simpa using hcw _ (by simp)

theorem hexOf_drop {dg : List Byte} {i : Nat} (hi : i < dg.length) :
    hexOf (dg.drop i) = hex2 (dg[i]'hi) ++ hexOf (dg.drop (i + 1)) := by
  unfold hexOf; rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]

/-- **The hex loop** from iteration `i` to the end: `stdout` receives the hex digits of the
digest's bytes `i … 31`. -/
theorem sha_hexLoop {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc)
    {Q : PState → Prop} {s0 : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    {dg : List Byte} :
    ∀ (k i : Nat) (v : PState), i + k = 32 → i < 32 →
    Body W (ShaMemP b lb sc) s0 v fr n saved → v.m.core.rip = b + 0x2bc8#64 →
    loadN v.m.memory (b + 0xa178#64) 8 = some 64#64 →
    v.m.core.read .r13 = BitVec.ofNat 64 i → v.m.core.read .r14 = b + 0x7238#64 →
    v.m.memory.readBytes (v.m.core.read .rbx).toNat 32 = some dg →
    (v.m.core.read .rsp).toNat ≤ (v.m.core.read .rbx).toNat →
    ∀ st, StdoutIs E v.m.memory st →
    (∀ w st', Body W (ShaMemP b lb sc) s0 w fr n saved → w.m.core.rip = b + 0x2bef#64 →
      w.m.core.read .rsp = v.m.core.read .rsp →
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], w.m.core.read r = v.m.core.read r) →
      StdoutIs E w.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      w.g.out ++ st'.buf = v.g.out ++ st.buf ++ hexOf (dg.drop i) →
      w.g.jobs = v.g.jobs → w.g.atexit = v.g.atexit → w.g.done = none →
      (w.g.inp = v.g.inp ∧ w.g.allocs = v.g.allocs ∧ w.g.heap = v.g.heap ∧
        w.g.files = v.g.files) → w.g.err = v.g.err →
      Keeps (fun a => W.Kept a ∨ (v.m.core.read .rsp).toNat ≤ a) v.m.memory w.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file v.m.memory f st'' → E.S.file w.m.memory f st'') →
      LibK E W v.m.memory w.m.memory → MustQ W Q w) →
    MustQ W Q v := by
  intro k
  induction k with
  | zero => intro i v h1 h2; omega
  | succ k ih =>
    intro i v hk hi hB hrip hlen hr13 hr14 hdg hdgs st hst kk
    have hdl : dg.length = 32 := Silmaril.Process.Memory.readWith_length hdg
    refine sha_hexStep I hB hrip hlo hfr hn hsv hal hrel hlen hi hr13 hr14 hdg hst ?_
    intro w st' hBw hripw hrspw hcw hr13w hstw herr hrd heof hrdg hout hj ha hdn hii hie hkw how hLw
    by_cases hlt : i + 1 < 32
    · simp only [hlt, ↓reduceIte] at hripw
      have hrbx := hcw .rbx (by simp)
      have hr14w := hcw .r14 (by simp)
      have e : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by have := I.hb; omega)
      refine ih (i + 1) w (by omega) hlt hBw hripw (by
          rw [loadN_keeps hkw (fun j hj => Or.inl (Or.inl (show W.InImage _ by
            rw [I.img, e]; exact ⟨by omega, by omega⟩)))]
          exact hlen) hr13w (by rw [hr14w, hr14]) ?_ (by rw [hrspw, hrbx]; exact hdgs)
        st' hstw ?_
      · rw [hrbx, hkw.readBytes (fun j hj => Or.inr (by omega))]; exact hdg
      · intro w2 st2 hB2 hrip2 hrsp2 hc2 hst2 herr2 hrd2 heof2 hrdg2 hout2 hj2 ha2 hdn2 hii2 hie2 hk2 ho2 hL2
        refine kk w2 st2 hB2 hrip2 (by rw [hrsp2, hrspw]) (fun r hr => by rw [hc2 r hr, hcw r hr]) hst2
          (by rw [herr2, herr]) (by rw [hrd2, hrd]) (by rw [heof2, heof]) (by rw [hrdg2, hrdg]) ?_ (by rw [hj2, hj])
          (by rw [ha2, ha]) hdn2 ⟨by rw [hii2.1, hii.1], by rw [hii2.2.1, hii.2.1], by rw [hii2.2.2.1, hii.2.2.1],
            by rw [hii2.2.2.2, hii.2.2.2]⟩ (by rw [hie2, hie]) (hkw.trans (by rw [← hrspw]; exact hk2))
          (fun f s'' hne hf => ho2 f s'' hne (how f s'' hne hf)) (hLw.trans hL2)
        rw [hout2, hout, hexOf_drop (i := i) (by omega)]; simp
    · simp only [hlt, ↓reduceIte] at hripw
      have hi31 : i = 31 := by omega
      subst hi31
      refine kk w st' hBw hripw hrspw hcw hstw herr hrd heof hrdg ?_ hj ha hdn hii hie hkw how hLw
      rw [hout, hexOf_drop (by omega)]
      simp [hexOf, List.drop_eq_nil_of_le (show dg.length ≤ 31 + 1 by omega)]

end Silmaril.Elf.Link.Dyn.Sha256sum
