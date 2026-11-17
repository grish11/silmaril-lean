module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MainSpn

/-! # GNU `sha256sum`: calls from `main`'s body, and program stores outside its frame

* `main_call`: a call through a `.plt.sec` stub to an import whose contract returns with the
  library frame `LibRet` and keeps every stream; the body, the library state `MEnv`, the
  callee-saved registers and the library ghost carry over.
* `body_rebase`: after a program store outside the stack room (into the image's option
  variables or a libc cell), the body continues from a new base state with the same registers
  (the caller's return address is unchanged).
* `exec_storeq_rip`: `mov [rip + d], src`.
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

/-- `mov [rip + d], src` (64-bit). -/
theorem exec_storeq_rip (d : BitVec 32) (src : Reg) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.rip + BitVec.ofNat 64 l + d.signExtend 64).toNat 8) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.mov .q (.mem (Silmaril.X86.Ext.Mem.ofRip d)) src))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.rip + BitVec.ofNat 64 l + d.signExtend 64) 8 (c.read src)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, ofRip_addr, storeN_ok h, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.bytes]

/-- A framed quiet contract (`setlocale`, `bindtextdomain`, `textdomain`) with its frame. -/
theorem framedQuiet_imp {E : Env} {W : World} {P : Word → Prop} {s : PState}
    {r : Silmaril.X86.RelIsa.Res PState} (h : framed E W (fun _ _ => False) (quietStep W P) s r) :
    Contract (AbiEntry s.m.core s.m.memory)
      (fun t => LibRet E W (fun _ => False) s t ∧ OthersKept E s t [] ∧ t.g = s.g ∧ P (t.m.core.read .rax)) r := by
  intro hp
  obtain ⟨t, rfl, ht⟩ := h.1 hp
  obtain ⟨hl, ho⟩ := h.2.1 (fun a h => h.elim) t rfl
  exact ⟨t, rfl, hl, ho, ht.2.2, ht.2.1⟩

/-- **A body after a store outside its stack room** continues from a new base. -/
theorem body_rebase {W : World} {b lb kb sr sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64)
    {s u : PState} {fr n : Nat} {sv : List (Nat × Word)}
    (hB : Body W (ShaMemAll b lb kb sr sc) s u fr n sv) (hsv : ∀ p ∈ sv, 8 ≤ p.1 ∧ p.1 ≤ n) {m' : Memory}
    (hk : Keeps (fun x => ImgW b x ∨ ((s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8))
      u.m.memory m')
    (hperm : ∀ x acc, m'.permits acc x = u.m.memory.permits acc x) {c : State}
    (hc : c.read .rsp = u.m.core.read .rsp) (hcf : c.fsBase = u.m.core.fsBase) :
    Body W (ShaMemAll b lb kb sr sc) ⟨⟨s.m.core, m'⟩, s.g⟩ ⟨⟨c, m'⟩, u.g⟩ fr n sv ∧
      m'.readBytes (s.m.core.read .rsp).toNat 8 = s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 := by
  have hroom := hB.room
  have hn := hroom.1
  refine ⟨⟨hc.trans hB.rsp, Keeps.refl _ _ |>.mono fun _ _ => trivial, hroom.keeps fun x _ _ acc => hperm x acc,
    hB.mem.keepW hb (hk.mono fun _ h => Or.inl h), hcf.trans hB.fs, hB.done, fun p hp => ?_,
    fun _ _ _ _ => rfl⟩, ?_⟩
  · have := hsv p hp
    dsimp only
    rw [hk.readBytes (fun j hj => Or.inr ⟨by omega, by omega⟩)]
    exact hB.saved p hp
  · rw [hk.readBytes (fun j hj => Or.inr ⟨by omega, by omega⟩)]
    exact hB.keep.readBytes (fun j hj => Or.inr (by omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A call of a contracted import from `main`'s body**, also keeping the cells `C` (K8: the
library keeps its non-private memory outside the call's footprint). -/
theorem main_callC {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s u : PState}
    (hB : Body W (ShaMemAll b lb kb sr sc) s u 328 4096 (sv6 s)) (hal : (s.m.core.read .rsp).toNat % 16 = 8)
    (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (henv : MEnv E W b lb C fi sto ste sti u.m.memory)
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    (hL : listingOk code L = true) (hl : ∀ m, ShaMemAll b lb kb sr sc m → Loaded m base code)
    {o : Nat} {rel : BitVec 32} (hlk : L.lookup o = some (.ext8 (.base (.call rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    {so : Nat} {disp : BitVec 32}
    (hs1 : pltSecListing.lookup so = some (.ext8 (.base .endbr64), 4))
    (hs2 : pltSecListing.lookup (so + 4) = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = b + 0x23c0#64 + BitVec.ofNat 64 so)
    (hso : so + 10 < 0x380)
    {a : Word} {nm : Name} {c : PState → Silmaril.X86.RelIsa.Res PState → Prop} (hI : ImpOk W a nm c)
    (hslot : ∀ m, ShaMemAll b lb kb sr sc m →
      loadN m (b + 0x23c0#64 + BitVec.ofNat 64 (so + 4 + 6) + disp.signExtend 64) 8 = some a)
    {pre : Prop} {R : PState → Prop} {fp : Nat → Prop}
    (hx : ∀ r, c (callEntry u a (base + BitVec.ofNat 64 (o + 5))) r →
      Contract pre (fun t => LibRet E W fp (callEntry u a (base + BitVec.ofNat 64 (o + 5))) t ∧
        OthersKept E (callEntry u a (base + BitVec.ofNat 64 (o + 5))) t [] ∧
        t.g = u.g ∧ R t) r)
    (hpre : AbiEntry (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.core
      (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory →
      MEnv E W b lb C fi sto ste sti (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory → pre)
    (hfp : ∀ x, fp x → ¬ W.Kept x ∧ ¬ C x ∧ x + 48 < (s.m.core.read .rsp).toNat)
    (k : ∀ v, R v → Body W (ShaMemAll b lb kb sr sc) s v 328 4096 (sv6 s) →
      v.m.core.rip = base + BitVec.ofNat 64 (o + 5) → v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) → v.g = u.g →
      MEnv E W b lb C fi sto ste sti v.m.memory →
      Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - 328 ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory →
      Keeps C u.m.memory v.m.memory → MustQ W Q v) :
    MustQ W Q u := by
  have hroom := hB.room
  have hsp := hroom.1
  have hMk := shaMemAll_keepI (lb := lb) (kb := kb) (sr := sr) (sc := sc) I hb
  have hwsp : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 328 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by omega)
  have hw8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hwsp]; omega
  have hpushK : ∀ x, (u.m.core.read .rsp - 8#64).toNat ≤ x → x < (u.m.core.read .rsp - 8#64).toNat + 8 →
      ¬ W.Kept x ∧ ¬ C x := by
    intro x h1 h2
    rw [hw8] at h1 h2
    exact ⟨(hroom.2.2 x (by omega) (by omega)).2.2, fun hc => by have := hC x hc; omega⟩
  have henvE : MEnv E W b lb C fi sto ste sti
      (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory := by
    rw [callEntry_mem]; exact henv.push (by rw [hw8]; omega) hpushK
  refine body_callK hMk hB (by decide) (by decide) (sv6_bound328 s) (by omega) hlz
    (o := o) (so := so) (pb := b + 0x23c0#64) (fp := fp)
    hL hlk hin hl hrip shaC_listing_ok.1 hs1 hs2 htgt
    (img_off I hb (by omega)) (img_off I hb (by omega)) (fun m h => h.cl.plt) hslot
    hI.1 hI.2.1 hI.2.2.1 (fun r h => hx r ((impOk_fn hI _ r).1 h))
    (fun he => hpre he henvE)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.2.1]; exact hB.done⟩)
    (fun x h => ⟨(hfp x h).1, Or.inl (by have := (hfp x h).2.2; omega)⟩) (fun x h => h.elim) ?_
  intro v hv hBv hrv hspv hcsv hkv
  obtain ⟨hlv, hov, hgv, hRv⟩ := hv
  have hkC1 : Keeps C u.m.memory (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory := by
    rw [callEntry_mem]; exact pushMem_keeps fun x hx => by rw [hw8]; have := hC x hx; omega
  have hkC2 : Keeps C (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory v.m.memory :=
    hlv.2.2.2.1.mono fun x hx => ⟨(henvE.np x (Or.inr hx)).1, fun hf => (hfp x hf).2.1 hx, (henvE.np x (Or.inr hx)).2⟩
  exact k v hRv hBv hrv hspv hcsv hgv
    (MEnv.lib I henvE hlv hov (fun x h => ⟨(hfp x h).1, (hfp x h).2.1⟩))
    (hkv.mono fun x hx => hx) (hkC1.trans hkC2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A call of a contracted import from `main`'s body.** -/
theorem main_call {E : Env} {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    {C : Nat → Prop} {fi : Word} {sto ste sti : St} {Q : PState → Prop} {s u : PState}
    (hB : Body W (ShaMemAll b lb kb sr sc) s u 328 4096 (sv6 s)) (hal : (s.m.core.read .rsp).toNat % 16 = 8)
    (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (henv : MEnv E W b lb C fi sto ste sti u.m.memory)
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    (hL : listingOk code L = true) (hl : ∀ m, ShaMemAll b lb kb sr sc m → Loaded m base code)
    {o : Nat} {rel : BitVec 32} (hlk : L.lookup o = some (.ext8 (.base (.call rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    {so : Nat} {disp : BitVec 32}
    (hs1 : pltSecListing.lookup so = some (.ext8 (.base .endbr64), 4))
    (hs2 : pltSecListing.lookup (so + 4) = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = b + 0x23c0#64 + BitVec.ofNat 64 so)
    (hso : so + 10 < 0x380)
    {a : Word} {nm : Name} {c : PState → Silmaril.X86.RelIsa.Res PState → Prop} (hI : ImpOk W a nm c)
    (hslot : ∀ m, ShaMemAll b lb kb sr sc m →
      loadN m (b + 0x23c0#64 + BitVec.ofNat 64 (so + 4 + 6) + disp.signExtend 64) 8 = some a)
    {pre : Prop} {R : PState → Prop} {fp : Nat → Prop}
    (hx : ∀ r, c (callEntry u a (base + BitVec.ofNat 64 (o + 5))) r →
      Contract pre (fun t => LibRet E W fp (callEntry u a (base + BitVec.ofNat 64 (o + 5))) t ∧
        OthersKept E (callEntry u a (base + BitVec.ofNat 64 (o + 5))) t [] ∧
        t.g = u.g ∧ R t) r)
    (hpre : AbiEntry (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.core
      (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory →
      MEnv E W b lb C fi sto ste sti (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory → pre)
    (hfp : ∀ x, fp x → ¬ W.Kept x ∧ ¬ C x ∧ x + 48 < (s.m.core.read .rsp).toNat)
    (k : ∀ v, R v → Body W (ShaMemAll b lb kb sr sc) s v 328 4096 (sv6 s) →
      v.m.core.rip = base + BitVec.ofNat 64 (o + 5) → v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) → v.g = u.g →
      MEnv E W b lb C fi sto ste sti v.m.memory →
      Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - 328 ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory →
      MustQ W Q v) :
    MustQ W Q u :=
  main_callC I hb hlz hB hal hlo hC henv hL hl hlk hin hrip hs1 hs2 htgt hso hI hslot hx hpre hfp
    fun v hR hBv hrv hspv hcsv hgv hE hK _ => k v hR hBv hrv hspv hcsv hgv hE hK

end Silmaril.Elf.Link.Dyn.Sha256sum
