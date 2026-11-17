module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemMain
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestOpen

/-! # GNU `sha256sum`: `main`'s prologue

`main` (`0x2750`): `endbr64`, six pushes (`rbp`, `r15`, `r14`, `r13`, `r12`, `rbx`) and a
`0x118`-byte frame: a body (`Proc.Frame.Body`) with a 328-byte frame, up to `0x2768`.
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
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

/-- The image facts of `main`'s body, kept by every frame that keeps the image. -/
theorem shaMemAll_keepI {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) :
    ∀ m m', ShaMemAll b lb kb sr sc m → Keeps W.InImage m m' → ShaMemAll b lb kb sr sc m' :=
  fun _ _ hm h => hm.keep hb (by rw [I] at h; exact h)

/-- What holds at the end of `main`'s prologue (`0x2768`). -/
structure MainPro (W : World) (b lb kb sr sc : Word) (s u : PState) : Prop where
  body : Body W (ShaMemAll b lb kb sr sc) s u 328 4096 (sv6 s)
  rip : u.m.core.rip = b + 0x2768#64
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rdi : u.m.core.read .rdi = s.m.core.read .rdi
  rsi : u.m.core.read .rsi = s.m.core.read .rsi
  g : u.g = s.g
  regs : u.m.memory.regions = s.m.memory.regions
  low : ∀ a, a < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ a →
    u.m.memory.bytes.get? a = s.m.memory.bytes.get? a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`main`'s prologue** (`0x2750`–`0x2768`). -/
theorem sha_main_pro {W : World} {b lb kb sr sc : Word} (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x2750#64) (hroom : Room W s.m.memory (s.m.core.read .rsp) 4096)
    (hd : s.g.done = none) (hm : ShaMemAll b lb kb sr sc s.m.memory)
    (k : ∀ u, MainPro W b lb kb sr sc s u → MustQ W Q u) : MustQ W Q s := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have e32 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 32 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e24]; omega
  have e40 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e32]; omega
  have e48 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 48 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e40]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have p2 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r2 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have p3 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r3 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have p4 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r4 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have p5 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r5 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have p6 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r6 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hMk := shaMemAll_keepI (lb := lb) (kb := kb) (sr := sr) (sc := sc) I hb
  have hm1 := hMk _ _ hm (room_push_img (v := s.m.core.read .rbp) (sp' := s.m.core.read .rsp) hroom
    (by omega) (by omega))
  have hm2 := hMk _ _ hm1 (room_push_img (v := s.m.core.read .r15) (sp' := s.m.core.read .rsp - 8#64) hroom
    (by rw [e8]; omega) (by rw [e8]; omega))
  have hm3 := hMk _ _ hm2 (room_push_img (v := s.m.core.read .r14) (sp' := s.m.core.read .rsp - 8#64 - 8#64) hroom
    (by rw [e16]; omega) (by rw [e16]; omega))
  have hm4 := hMk _ _ hm3 (room_push_img (v := s.m.core.read .r13) (sp' := s.m.core.read .rsp - 8#64 - 8#64 - 8#64) hroom
    (by rw [e24]; omega) (by rw [e24]; omega))
  have hm5 := hMk _ _ hm4 (room_push_img (v := s.m.core.read .r12) (sp' := s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64) hroom
    (by rw [e32]; omega) (by rw [e32]; omega))
  have hm6 := hMk _ _ hm5 (room_push_img (v := s.m.core.read .rbx) (sp' := s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) hroom
    (by rw [e40]; omega) (by rw [e40]; omega))
  refine must_listed (o := 0) shaM_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide)) hm.mn.mainA
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  xstep [hrip]
  refine must_listed (o := 4) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm.mn.mainA (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 5) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm1.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 8) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm1.mn.mainA (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p2)]
  xstep []
  refine must_listed (o := 10) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm2.mn.mainA (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p3)]
  xstep []
  refine must_listed (o := 12) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm3.mn.mainA (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p4)]
  xstep []
  refine must_listed (o := 14) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm4.mn.mainA (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p5)]
  xstep []
  refine must_listed (o := 16) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm5.mn.mainA (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p6)]
  xstep []
  refine must_listed (o := 17) shaM_listing_ok.1 rfl hd (hin _ (by decide)) hm6.mn.mainA (by rw [ripadd]) ?_
  xstep []
  refine k _ ⟨⟨?_, (((((((room_push_caller hroom (by omega) (by omega)).trans
      (room_push_caller hroom (by rw [e8]; omega) (by rw [e8]; omega))).trans
      (room_push_caller hroom (by rw [e16]; omega) (by rw [e16]; omega))).trans
      (room_push_caller hroom (by rw [e24]; omega) (by rw [e24]; omega))).trans
      (room_push_caller hroom (by rw [e32]; omega) (by rw [e32]; omega))).trans
      (room_push_caller hroom (by rw [e40]; omega) (by rw [e40]; omega)))).mono fun _ ha => ha.1,
      hroom.pushMem.pushMem.pushMem.pushMem.pushMem.pushMem, hm6, rfl, hd, ?_,
    fun a _ _ acc => by simp [pushMem_permits]⟩, ?_, by simp, by simp, by simp, rfl, by simp, ?_⟩
  · simp [BitVec.sub_sub]
  · intro q hq
    simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only
      rw [read_push_ne (by rw [e48, e40]; omega) (by rw [e40]; omega) (by rw [e40]; omega),
        read_push_ne (by rw [e40, e32]; omega) (by rw [e32]; omega) (by rw [e32]; omega),
        read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
        read_push_ne (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
        read_push_ne (by rw [e16, e8]; omega) (by rw [e8]; omega) (by rw [e8]; omega)]
      exact push_read_at r1 p1 e8
    · simp only
      rw [read_push_ne (by rw [e48, e40]; omega) (by rw [e40]; omega) (by rw [e40]; omega),
        read_push_ne (by rw [e40, e32]; omega) (by rw [e32]; omega) (by rw [e32]; omega),
        read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
        read_push_ne (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
        show (s.m.core.read .rsp).toNat - 16 = (s.m.core.read .rsp - 8#64).toNat - 8 by rw [e8]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r2) (by simpa [pushMem_permitted] using p2)
        (by rw [e16, e8]; omega)
    · simp only
      rw [read_push_ne (by rw [e48, e40]; omega) (by rw [e40]; omega) (by rw [e40]; omega),
        read_push_ne (by rw [e40, e32]; omega) (by rw [e32]; omega) (by rw [e32]; omega),
        read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
        show (s.m.core.read .rsp).toNat - 24 = (s.m.core.read .rsp - 8#64 - 8#64).toNat - 8 by rw [e16]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r3) (by simpa [pushMem_permitted] using p3)
        (by rw [e24, e16]; omega)
    · simp only
      rw [read_push_ne (by rw [e48, e40]; omega) (by rw [e40]; omega) (by rw [e40]; omega),
        read_push_ne (by rw [e40, e32]; omega) (by rw [e32]; omega) (by rw [e32]; omega),
        show (s.m.core.read .rsp).toNat - 32 = (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat - 8 by rw [e24]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r4) (by simpa [pushMem_permitted] using p4)
        (by rw [e32, e24]; omega)
    · simp only
      rw [read_push_ne (by rw [e48, e40]; omega) (by rw [e40]; omega) (by rw [e40]; omega),
        show (s.m.core.read .rsp).toNat - 40 = (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat - 8 by rw [e32]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r5) (by simpa [pushMem_permitted] using p5)
        (by rw [e40, e32]; omega)
    · simp only
      rw [show (s.m.core.read .rsp).toNat - 48 = (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat - 8 by rw [e40]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r6) (by simpa [pushMem_permitted] using p6)
        (by rw [e48, e40]; omega)
  · rfl
  · intro a ha
    have k1 := (pushMem_keeps (m := s.m.memory) (sp := s.m.core.read .rsp) (v := s.m.core.read .rbp)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e8]; omega)) a ha
    have k2 := (pushMem_keeps (m := (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))) (sp := s.m.core.read .rsp - 8#64) (v := s.m.core.read .r15)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e16]; omega)) a ha
    have k3 := (pushMem_keeps (m := (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) (s.m.core.read .rsp - 8#64) (s.m.core.read .r15))) (sp := s.m.core.read .rsp - 8#64 - 8#64) (v := s.m.core.read .r14)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e24]; omega)) a ha
    have k4 := (pushMem_keeps (m := (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) (s.m.core.read .rsp - 8#64) (s.m.core.read .r15)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r14))) (sp := s.m.core.read .rsp - 8#64 - 8#64 - 8#64) (v := s.m.core.read .r13)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e32]; omega)) a ha
    have k5 := (pushMem_keeps (m := (pushMem (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) (s.m.core.read .rsp - 8#64) (s.m.core.read .r15)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r14)) (s.m.core.read .rsp - 8#64 - 8#64 - 8#64) (s.m.core.read .r13))) (sp := s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64) (v := s.m.core.read .r12)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e40]; omega)) a ha
    have k6 := (pushMem_keeps (m := (pushMem (pushMem (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) (s.m.core.read .rsp - 8#64) (s.m.core.read .r15)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r14)) (s.m.core.read .rsp - 8#64 - 8#64 - 8#64) (s.m.core.read .r13)) (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64) (s.m.core.read .r12))) (sp := s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) (v := s.m.core.read .rbx)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e48]; omega)) a ha
    rw [k6.1, k5.1, k4.1, k3.1, k2.1, k1.1]

end Silmaril.Elf.Link.Dyn.Sha256sum
