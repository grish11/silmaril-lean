module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintPutc

/-! # sha256sum's output path, part (d): the escape test

`sha_escChk`: at `0x35b6`, with the line delimiter `\n`, `main` asks
`strcspn (name, "\\\n\r")`; for a name with none of these bytes the answer is its length, the
byte there is the terminating `NUL`, and control returns to `0x2ba7` with no escaping.
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

/-- The bytes `strcspn` is asked to reject. -/
def rejectBytes : List Byte := [0x5c#8, 0x0a#8, 0x0d#8]

theorem takeWhile_none {name : List Byte} (h : ∀ c ∈ name, c ∉ rejectBytes) :
    name.takeWhile (fun c => !rejectBytes.contains c) = name := by
  induction name with
  | nil => rfl
  | cons c t ih =>
    have hc := h c (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    have e : (fun c => !rejectBytes.contains c) = (fun c => !decide (c ∈ rejectBytes)) := by
      funext x; simp
    rw [e] at ht
    simp [hc, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha_escChk {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x35b6#64)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0)
    {name : List Byte} (hname : CStr u.m.memory (u.m.core.read .r12) name)
    (hnr : ∀ c ∈ name, c ∉ rejectBytes)
    (hnk : ∀ j < name.length + 1, W.Kept ((u.m.core.read .r12).toNat + j))
    (hnp : ∀ j < name.length + 1, ¬ E.S.priv u.m.memory ((u.m.core.read .r12).toNat + j))
    (k : ∀ w, Body W (ShaMemP b lb sc) s0 w fr n saved → w.m.core.rip = b + 0x2ba7#64 →
      w.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, w.m.core.read r = u.m.core.read r) →
      (∀ f st, E.S.file u.m.memory f st → E.S.file w.m.memory f st) → w.g = u.g →
      CStr w.m.memory (w.m.core.read .r12) name →
      Keeps (fun a => W.Kept a ∨ (u.m.core.read .rsp).toNat ≤ a) u.m.memory w.m.memory →
      LibK E W u.m.memory w.m.memory → MustQ W Q w) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  refine must_listed (o := 0) shaP_listing_ok.2.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.escChk (by rw [hrip]; simp) ?_
  xstep [hrip]
  refine must_listed (o := 7) shaP_listing_ok.2.1 rfl hd (hin _ (by decide)) hB.mem.escChk
    (by rw [ripadd]) ?_
  xstep []
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by have := hB.room.1; omega) (by have := hB.room.1; omega)
  have hroom1 := hB.room.1
  have hlo8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hu]; omega
  have hpk : ∀ x : Word, Keeps (fun a => W.Kept a ∨ (u.m.core.read .rsp).toNat ≤ a ∨ E.S.lo > a) u.m.memory
      (pushMem u.m.memory (u.m.core.read .rsp) x) := fun x => pushMem_keeps fun y hy => by
    rw [sub_toNat (k := 8) (by omega) (by decide)]
    rcases hy with h | h | h
    · by_cases hc : (s0.m.core.read .rsp).toNat - n ≤ y ∧ y < (s0.m.core.read .rsp).toNat + 8
      · exact absurd h (hB.room.2.2 y hc.1 hc.2).2.2
      · omega
    · omega
    · omega
  have hcsp : ∀ x : Word, CStr (pushMem u.m.memory (u.m.core.read .rsp) x) (u.m.core.read .r12) name := fun x =>
    ⟨hname.1, by rw [(hpk x).readBytes (fun j hj => Or.inl (hnk j hj))]; exact hname.2⟩
  have hpush : ∀ x : Word, ShaMemP b lb sc (pushMem u.m.memory (u.m.core.read .rsp) x) := fun x =>
    shaMemP_keep I.img I.hb _ _ hB.mem (by
      rw [I.img]; exact img_push I.img hB.room (by rw [hu]; omega) (by rw [hu]; omega))
  refine must_gen (fun x => x.m.core.rip = b + 13760#64 ∧ x.m.core.read .rsi = b + 0x71e0#64 ∧
      x.m.core.read .rdi = u.m.core.read .r12 ∧ x.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, x.m.core.read r = u.m.core.read r) ∧
      x.m.memory = u.m.memory ∧ x.g = u.g ∧ x.m.core.fsBase = u.m.core.fsBase)
    ⟨rfl, by simp, by simp, by simp, fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro x ⟨hxr, hxsi, hxdi, hxsp, hxc, hxm, hxg, hxf⟩
  have hBx : Body W (ShaMemP b lb sc) s0 x fr n saved := hB.of_eq hxm hxsp hxf (by rw [hxg])
  have hr12x : x.m.core.read .r12 = u.m.core.read .r12 := hxc .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])
  refine body_call (shaMemP_keep I.img I.hb) hBx hfr hn hsv hal I.lz
    (o := 10) (so := 48) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaP_listing_ok.2.1 rfl (by rw [hxr]; exact hin _ (by decide)) (fun m h => h.escChk) (by rw [hxr, ripadd])
    shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (48 + 4 + 6) + BitVec.signExtend 64 0x79f6#32 =
        b + 0x9df0#64 by simp only [BitVec.add_assoc]; rfl]
      exact h.strcspn)
    I.strcspn.1 I.strcspn.2.1 I.strcspn.2.2.1 (fun r h => (impOk_fn I.strcspn _ r).1 h)
    (fun habi => ⟨habi, ⟨name, ?c1⟩, ⟨rejectBytes, ?c2⟩⟩)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, by rw [hw.2.1]; simpa using hBx.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  case c1 =>
    rw [callEntry_mem, callEntry_read _ _ _ (by decide), hxdi, hxm, hxsp]; exact hcsp _
  case c2 =>
    rw [callEntry_mem, callEntry_read _ _ _ (by decide), hxsi, hxm, hxsp]
    exact ⟨by decide, (hpush _).reject⟩
  intro w hw hB2 hrip2 hrsp2 hcs2
  have hLw : LibK E W u.m.memory w.m.memory := ((LibK.refl E W _).of_eq hxm).call0 (by rw [hxsp]; exact hlo8) hw.1
  obtain ⟨⟨⟨-, hkw⟩, -, -, hkp, -⟩, hgw, hok, hrax⟩ := hw
  have hdw : w.g.done = none := hB2.done
  -- the name is still there (it is mapped and not private)
  have hpriv : ∀ y : Word, E.S.priv (pushMem u.m.memory (u.m.core.read .rsp) y) = E.S.priv u.m.memory := fun y =>
    E.S.priv_local _ _ fun a ha => ⟨((hpk y) a (Or.inr (Or.inr ha))).1, ((hpk y) a (Or.inr (Or.inr ha))).2⟩
  obtain ⟨hra, hrw, hrp⟩ := Streams.Total.perm_of_read hname.2
  have hcw : CStr w.m.memory (w.m.core.read .r12) name := by
    rw [hcs2 .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr12x]
    refine ⟨hname.1, ?_⟩
    have hkp' : Keeps (fun a => ¬ E.S.priv u.m.memory a ∧ ¬ False ∧ u.m.memory.permits .read a = true)
        (pushMem u.m.memory (u.m.core.read .rsp) (b + 0x35b6#64 + BitVec.ofNat 64 (10 + 5))) w.m.memory := by
      simpa [callEntry_mem, hxm, hxsp, hpriv, pushMem_permits] using hkp
    rw [← (hcsp (b + 0x35b6#64 + BitVec.ofNat 64 (10 + 5))).2]
    exact hkp'.readBytes (fun j hj => ⟨hnp j hj, id, hrp j hj⟩)
  have hraxw : w.m.core.read .rax = BitVec.ofNat 64 name.length := by
    rw [hrax name rejectBytes
      (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hxdi, hxm, hxsp]; exact hcsp _)
      (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hxsi, hxm, hxsp]; exact ⟨by decide, (hpush _).reject⟩)]
    rw [takeWhile_none hnr]
  have hr12w : w.m.core.read .r12 = u.m.core.read .r12 := by
    rw [hcs2 .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr12x]
  have hz : loadN w.m.memory (w.m.core.read .r12 + w.m.core.read .rax) 1 = some 0#64 := by
    have hsub := Streams.Total.sub_read hcw.2 (k := name.length) (j := 1) (by omega) (by omega)
    rw [hr12w] at hsub
    have ha : (u.m.core.read .r12 + BitVec.ofNat 64 name.length).toNat = (u.m.core.read .r12).toNat + name.length := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := name.length) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [hraxw, hr12w]
    simp only [loadN, ha, hsub, Option.map_some]
    simp [List.drop_append_of_le_length (le_refl _), Silmaril.X86.Ext.leValue]
  refine must_listed (o := 15) shaP_listing_ok.2.1 rfl hdw (by rw [hrip2, ripadd]; exact hin _ (by decide))
    hB2.mem.escChk (by rw [hrip2, ripadd]) ?_
  rw [exec_cmpb0_idx _ _ _ 0#64 hz]
  simp only [WP_ok, hrip2, ripadd]
  refine must_listed (o := 20) shaP_listing_ok.2.1 rfl hdw (hin _ (by decide)) hB2.mem.escChk
    (by rw [ripadd]) ?_
  xstep [eval_e_sub]
  refine k _ (hB2.of_eq rfl (by simp) rfl rfl) (by rfl) (by simp [hrsp2, hxsp]) (fun r hr => ?_) ?_
    (by simp [hgw, hxg]) (by simpa using hcw) ?_ hLw
  · have : r ≠ .rsp := fun h => Silmaril.X86.sysv64_rsp_not_calleeSaved (h ▸ hr)
    simp only [Silmaril.X86.State.read_mk_regs]
    rw [hcs2 r hr, hxc r hr]
  · intro f st h
    exact hok f st (by simp) (by rw [callEntry_mem, hxm, hxsp]; exact file_push h hlo8)
  · rw [← hxm]
    refine (pushMem_keeps fun y hy => ?_).trans (hkw.mono fun y hy => ⟨?_, id⟩)
    · rw [hxsp, sub_toNat (k := 8) (by omega) (by decide)]
      rcases hy with h | h
      · by_cases hc : (s0.m.core.read .rsp).toNat - n ≤ y ∧ y < (s0.m.core.read .rsp).toNat + 8
        · exact absurd h (hB.room.2.2 y hc.1 hc.2).2.2
        · omega
      · omega
    · rcases hy with h | h
      · exact Or.inl h
      · right; rw [callEntry_rsp, hxsp, sub_toNat (k := 8) (by omega) (by decide)]; omega

end Silmaril.Elf.Link.Dyn.Sha256sum
