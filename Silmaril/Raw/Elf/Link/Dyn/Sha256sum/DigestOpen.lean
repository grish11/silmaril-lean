module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FopenSafer
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Exec

/-! # GNU `sha256sum`: `digest_file` up to its read loop

`digest_file (filename, bin_result, missing)` (`0x6a40`, gnulib's `sha256_stream` inlined) on a
readable file: the prologue, `*missing = false`, `fopen_safer`, `fileno`/`posix_fadvise`,
`malloc (BLOCKSIZE + 72)`, `SHA256_Init`, up to the loop head `0x6b27` (`DigInv`).
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

/-- The imports `digest_file` calls. -/
structure DigImps (E : Env) (R : ShaRep) (W : World) (b lb kb : Word) : Prop where
  cl : CloseImps E W b lb
  lseek : ImpOk W (lb + 0x11b2a0#64) (nm "lseek") (lseekStep E W)
  fopen : ImpOk W (lb + 0x85f40#64) (nm "fopen") (fopenStep E W)
  fadvise : ImpOk W (lb + 0x11b7f0#64) (nm "posix_fadvise") (fadviseStep E W)
  malloc : ImpOk W (lb + 0xad750#64) (nm "malloc") (mallocStep E W)
  free : ImpOk W (lb + 0xade30#64) (nm "free") (freeStep E W)
  fread : ImpOk W (lb + 0x137130#64) (nm "__fread_unlocked_chk") (freadChkStep E W)
  init : ImpOk W (kb + 0x33d3c0#64) (nm "SHA256_Init")
    (framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256InitStep R W))
  update : ImpOk W (kb + 0x33d410#64) (nm "SHA256_Update")
    (framed E W (fun s => ctxRange (s.m.core.read .rdi)) (sha256UpdateStep R W))
  final : ImpOk W (kb + 0x33d630#64) (nm "SHA256_Final")
    (framed E W (fun s a => ctxRange (s.m.core.read .rsi) a ∨
      ((s.m.core.read .rdi).toNat ≤ a ∧ a < (s.m.core.read .rdi).toNat + 32)) (sha256FinalStep R W))
  alloc : E.allocOk = true

/-- A framed contract is within its contract with the frame added to the postcondition. -/
theorem framed_imp {E : Env} {W : World} {fp : PState → Nat → Prop} {pre : PState → Prop}
    {post : PState → PState → Prop} {s : PState} {r : Silmaril.X86.RelIsa.Res PState}
    (h : framed E W fp (fun s => Contract (pre s) (post s)) s r) :
    Contract (pre s ∧ ∀ a, fp s a → ¬ E.S.priv s.m.memory a)
      (fun t => post s t ∧ LibRet E W (fp s) s t ∧ OthersKept E s t []) r := by
  intro ⟨hp, hnp⟩
  obtain ⟨t, rfl, ht⟩ := h.1 hp
  exact ⟨t, rfl, ht, h.2.1 hnp t rfl⟩

/-- The saved registers of `digest_file`. -/
def sv6 (s : PState) : List (Nat × Word) :=
  [(8, s.m.core.read .rbp), (16, s.m.core.read .r15), (24, s.m.core.read .r14), (32, s.m.core.read .r13),
   (40, s.m.core.read .r12), (48, s.m.core.read .rbx)]

/-- The caller's objects `digest_file` writes: `*missing` and the 32-byte result. -/
def DX (s : PState) (a : Nat) : Prop :=
  ((s.m.core.read .rdx).toNat ≤ a ∧ a < (s.m.core.read .rdx).toNat + 1) ∨
  ((s.m.core.read .rsi).toNat ≤ a ∧ a < (s.m.core.read .rsi).toNat + 32)

/-- The caller's two output objects lie above the entry stack pointer, with their permissions
as at entry. -/
structure PermDX (s : PState) (m : Memory) : Prop where
  pos : ∀ a, DX s a → (s.m.core.read .rsp).toNat + 8 ≤ a
  perm : ∀ a, DX s a → ∀ acc, m.permits acc a = s.m.memory.permits acc a

theorem PermDX.keep {s : PState} {m m' : Memory} (h : PermDX s m) {P : Nat → Prop} (hk : Keeps P m m')
    (hP : ∀ a, DX s a → (s.m.core.read .rsp).toNat + 8 ≤ a → P a) : PermDX s m' :=
  ⟨h.pos, fun a ha acc => by rw [(hk a (hP a ha (h.pos a ha))).2 acc]; exact h.perm a ha acc⟩

theorem PermDX.regions {s : PState} {m m' : Memory} (h : PermDX s m) (hr : m'.regions = m.regions) :
    PermDX s m' :=
  ⟨h.pos, fun a ha acc => by rw [← h.perm a ha acc]; unfold Memory.permits; rw [hr]⟩

/-- The byte `*missing`: the only caller object `digest_file` writes before `SHA256_Final`. -/
def MX (s : PState) (a : Nat) : Prop :=
  (s.m.core.read .rdx).toNat ≤ a ∧ a < (s.m.core.read .rdx).toNat + 1

theorem sv6_bound (s : PState) : ∀ p ∈ sv6 s, p.1 ≤ 48 ∧ 48 ≤ 216 := by
  intro q hq
  simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sv6_bound8 (s : PState) : ∀ p ∈ sv6 s, 8 ≤ p.1 ∧ p.1 ≤ 1024 := by
  intro q hq
  simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- What holds at `digest_file`'s prologue end (`0x6a57`). -/
structure DigPro (W : World) (b lb kb : Word) (s u : PState) : Prop where
  body : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) (MX s)
  rip : u.m.core.rip = b + 0x6a57#64
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  r12 : u.m.core.read .r12 = s.m.core.read .rdx
  rdi : u.m.core.read .rdi = s.m.core.read .rdi
  rsi : u.m.core.read .rsi = s.m.core.read .rsi
  g : u.g = s.g
  regs : u.m.memory.regions = s.m.memory.regions
  low : ∀ a, a < (s.m.core.read .rsp).toNat - 48 ∨ (s.m.core.read .rsp).toNat ≤ a →
    u.m.memory.bytes.get? a = s.m.memory.bytes.get? a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file`'s prologue** (`0x6a40`–`0x6a57`): six pushes, `r12 := missing`, a 216-byte frame. -/
theorem sha_digest_pro {E : Env} {W : World} {b lb kb : Word} (I : CloseImps E W b lb) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x6a40#64) (hroom : Room W s.m.memory (s.m.core.read .rsp) 1024)
    (hd : s.g.done = none) (hm : ShaMemCD b lb kb s.m.memory)
    (k : ∀ u, DigPro W b lb kb s u → MustQ W Q u) : MustQ W Q s := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
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
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.img I.hb
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
  refine must_listed (o := 0) shaD_listing_ok.2.2 rfl hd (by rw [hrip]; exact hin _ (by decide)) hm.2.digestFile
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep [hrip]
  refine must_listed (o := 1) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm1.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 4) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm1.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p2)]
  xstep []
  refine must_listed (o := 6) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm2.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p3)]
  xstep []
  refine must_listed (o := 8) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm3.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p4)]
  xstep []
  refine must_listed (o := 10) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm4.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p5)]
  xstep []
  refine must_listed (o := 12) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm5.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 15) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm5.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p6)]
  xstep []
  refine must_listed (o := 16) shaD_listing_ok.2.2 rfl hd (hin _ (by decide)) hm6.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine k _ ⟨⟨?_, (((((((room_push_caller hroom (by omega) (by omega)).trans
      (room_push_caller hroom (by rw [e8]; omega) (by rw [e8]; omega))).trans
      (room_push_caller hroom (by rw [e16]; omega) (by rw [e16]; omega))).trans
      (room_push_caller hroom (by rw [e24]; omega) (by rw [e24]; omega))).trans
      (room_push_caller hroom (by rw [e32]; omega) (by rw [e32]; omega))).trans
      (room_push_caller hroom (by rw [e40]; omega) (by rw [e40]; omega)))).mono fun _ ha => ha.1, hroom.pushMem.pushMem.pushMem.pushMem.pushMem.pushMem, hm6, rfl, hd, ?_,
    fun a _ _ acc => by simp [pushMem_permits]⟩, rfl, by simp, by simp, by simp, by simp, rfl, by simp, ?_⟩
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

theorem loadN_one {m : Memory} {a : Word} {x : Byte} (h : m.readBytes a.toNat 1 = some [x]) :
    loadN m a 1 = some (BitVec.ofNat 64 x.toNat) := by
  simp [loadN, h, Silmaril.X86.Ext.leValue]

/-- `sub r32, imm` as the semantics builds it. -/
abbrev subD (x y : BitVec 32) : Silmaril.X86.Flags :=
  @Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.Ext.Sz.d.bits Silmaril.X86.AluOp.sub x y

theorem eval_subD (x y : BitVec 32) (c : Silmaril.X86.Ext.Cond) :
    Silmaril.X86.Ext.Cond.eval (subD x y) c = some (Silmaril.X86.Ext.Cond.afterCmp (w := 31) x y c) :=
  Silmaril.X86.Ext.eval_subFlagsN (w := 31) x y c

/-- What holds at `0x6a88` (after `*missing = false`). -/
structure DigMid (E : Env) (W : World) (b lb kb : Word) (s x : PState) (g : Word) : Prop where
  body : BodyX W (ShaMemCD b lb kb) s x 216 1024 (sv6 s) (MX s)
  rbp : x.m.core.read .rbp = s.m.core.read .rsp - 8#64
  r12 : x.m.core.read .r12 = s.m.core.read .rdx
  slot1 : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 208) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rdi])
  slot2 : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 200) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rsi])
  slot3 : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  miss : x.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  low : ∀ a, a < E.S.lo → x.m.memory.bytes.get? a = s.m.memory.bytes.get? a ∧
    ∀ acc, x.m.memory.permits acc a = s.m.memory.permits acc a
  g : x.g = s.g
  regs : x.m.memory.regions = s.m.memory.regions

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file` from its prologue to `*missing = false`** (`0x6a57`–`0x6a88`): the frame slots
(file name, result pointer, stack guard) and `*missing = 0`. -/
theorem sha_digest_mid {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {Q : PState → Prop} {s u : PState} (hP : DigPro W b lb kb s u) (hlo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat)
    {p : List Byte} (hpk : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j))
    {c0 : Byte} (hc0 : s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [c0]) (hc0' : c0 ≠ 0x2d#8)
    (hX : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hmiss : s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 1)
    (hmissr : s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 1)
    {g : Word} (hg : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (k : ∀ x, DigMid E W b lb kb s x g → x.m.core.rip = b + 0x6a88#64 →
      BitVec.setWidth 32 (x.m.core.read .r14) ≠ 0#32 → MustQ W Q x) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hP.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.cl.img I.cl.hb
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  -- the three frame slots
  have a1 : (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat = (s.m.core.read .rsp).toNat - 208 := by
    rw [hP.rbp, show BitVec.signExtend 64 0xffffff38#32 = 0xffffffffffffff38#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw1 : u.m.memory.Permitted .write (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat 8 := by
    rw [a1]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  -- the memory as of `s` below the frame and above it (the path, the guard)
  have hkS : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 1024 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
      s.m.memory u.m.memory := fun a ha => ⟨hP.low a (by omega), fun acc => by simp only [Memory.permits, hP.regs]⟩
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 1024 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  set A1 := u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32 with hA1
  have hk1 : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 208 ∨ (s.m.core.read .rsp).toNat - 200 ≤ a)
      u.m.memory (storeMem u.m.memory A1 8 (u.m.core.read .rdi)) := storeMem_keeps fun x hx => by rw [a1]; omega
  have hc1 : (storeMem u.m.memory A1 8 (u.m.core.read .rdi)).readBytes (u.m.core.read .rdi).toNat 1 = some [c0] := by
    rw [hk1.readBytes (fun j hj => by rw [hP.rdi]; have := hKout _ (hpk 0 (by omega)); omega),
      hkS.readBytes (fun j hj => by rw [hP.rdi]; have := hKout _ (hpk 0 (by omega)); omega), hP.rdi]
    exact hc0
  refine must_listed (o := 23) shaD_listing_ok.2.2 rfl hB.done (by rw [hP.rip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hP.rip, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw1, WP_ok]
  refine must_listed (o := 30) shaD_listing_ok.2.2 rfl hB.done (by simp only [hP.rip, ripadd]; exact hin _ (by decide))
    (hMk _ _ hB.mem (hk1.mono fun x hx => by have := hKout x (Or.inl hx); omega)).2.digestFile
    (by simp only [hP.rip, ripadd]) ?_
  rw [exec_movzxb _ _ _ _ _ (BitVec.ofNat 64 c0.toNat) (by exact loadN_one hc1), WP_ok]
  -- an opaque state again
  refine must_gen (fun v => v.m.core.rip = b + 0x6a62#64 ∧ v.m.memory = storeMem u.m.memory A1 8 (u.m.core.read .rdi) ∧
      v.m.core.read .rbp = u.m.core.read .rbp ∧ v.m.core.read .r12 = u.m.core.read .r12 ∧
      v.m.core.read .rsi = u.m.core.read .rsi ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      BitVec.setWidth 32 (v.m.core.read .r14) = ((BitVec.ofNat 64 c0.toNat).setWidth 8).setWidth 32 ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ v.g = u.g ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r14 → v.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨by simp [hP.rip, ripadd], rfl, by simp [Silmaril.X86.Ext.Sz.write], by simp [Silmaril.X86.Ext.Sz.write],
      by simp [Silmaril.X86.Ext.Sz.write], by simp [Silmaril.X86.Ext.Sz.write], ?_, rfl, rfl, ?_⟩
    · simp [Silmaril.X86.Ext.Sz.write]
    · intro r hr hne
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl hne | simp [Silmaril.X86.Ext.Sz.write]
  rintro v ⟨hrv, hmv, hbpv, h12v, hsiv, hspv, h14v, hfsv, hgv, hcsv⟩
  have hmv' : ShaMemCD b lb kb v.m.memory := by
    rw [hmv]; exact hMk _ _ hB.mem (hk1.mono fun x hx => by have := hKout x (Or.inl hx); omega)
  have a2 : (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat = (s.m.core.read .rsp).toNat - 200 := by
    rw [hbpv, hP.rbp, show BitVec.signExtend 64 0xffffff40#32 = 0xffffffffffffff40#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw2 : v.m.memory.Permitted .write (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat 8 := by
    rw [a2, hmv, storeMem_permitted]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  refine must_listed (o := 34) shaD_listing_ok.2.2 rfl (by rw [hgv]; exact hB.done) (by rw [hrv]; exact hin _ (by decide))
    hmv'.2.digestFile (by rw [hrv, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw2, WP_ok]
  have hk2 : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 208 ∨ (s.m.core.read .rsp).toNat - 192 ≤ a)
      u.m.memory (storeMem v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 (v.m.core.read .rsi)) := by
    rw [hmv]
    exact (hk1.mono fun x hx => by omega).trans (storeMem_keeps fun x hx => by rw [a2]; omega)
  have hgk' : ∀ j, j < 8 → (s.m.core.fsBase + 0x28#64).toNat + j < (s.m.core.read .rsp).toNat - 1024 ∨
      (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.fsBase + 0x28#64).toNat + j := fun j hj => hKout _ (hgk j hj)
  have hgv2 : loadN (storeMem v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 (v.m.core.read .rsi))
      (v.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g := by
    rw [hfsv, hB.fs, show BitVec.signExtend 64 0x28#32 = 0x28#64 by decide,
      hk2.loadN (fun j hj => by have := hgk' j hj; omega), hkS.loadN (fun j hj => hgk' j hj)]
    exact hg
  refine must_listed (o := 41) shaD_listing_ok.2.2 rfl (by rw [hgv]; exact hB.done) (by simp only [hrv, ripadd]; exact hin _ (by decide))
    (hMk _ _ hB.mem (hk2.mono fun x hx => by have := hKout x (Or.inl hx); omega)).2.digestFile (by simp only [hrv, ripadd]) ?_
  rw [exec_loadfs _ _ _ _ _ _ (by exact hgv2), WP_ok]
  refine must_gen (fun w => w.m.core.rip = b + 0x6a72#64 ∧
      w.m.memory = storeMem v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 (v.m.core.read .rsi) ∧
      w.m.core.read .rax = g ∧
      w.m.core.read .rbp = u.m.core.read .rbp ∧ w.m.core.read .r12 = u.m.core.read .r12 ∧
      w.m.core.read .rsi = u.m.core.read .rsi ∧ w.m.core.read .rsp = u.m.core.read .rsp ∧
      BitVec.setWidth 32 (w.m.core.read .r14) = ((BitVec.ofNat 64 c0.toNat).setWidth 8).setWidth 32 ∧
      w.m.core.fsBase = u.m.core.fsBase ∧ w.g = u.g ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r14 → w.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨by simp [hrv, ripadd], rfl, by simp, by simp [hbpv], by simp [h12v], by simp [hsiv], by simp [hspv],
      by simpa using h14v, by simp [hfsv], hgv, ?_⟩
    intro r hr hne
    have hh := hcsv r hr hne
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp [hh]
  rintro w ⟨hrw, hmw, haxw, hbpw, h12w, hsiw, hspw, h14w, hfsw, hgw, hcsw⟩
  have a3 : (w.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat = (s.m.core.read .rsp).toNat - 64 := by
    rw [hbpw, hP.rbp, show BitVec.signExtend 64 0xffffffc8#32 = 0xffffffffffffffc8#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw3 : w.m.memory.Permitted .write (w.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat 8 := by
    rw [a3, hmw, storeMem_permitted, hmv, storeMem_permitted]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hmw' : ShaMemCD b lb kb w.m.memory := by
    rw [hmw]; exact hMk _ _ hB.mem (hk2.mono fun x hx => by have := hKout x (Or.inl hx); omega)
  refine must_listed (o := 50) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (by rw [hrw]; exact hin _ (by decide))
    hmw'.2.digestFile (by rw [hrw, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw3, WP_ok]
  have a3' : (w.m.core.read .rbp + 18446744073709551560#64).toNat = (s.m.core.read .rsp).toNat - 64 := a3
  have hx14 : BitVec.setWidth 32 (w.m.core.read .r14) ≠ 45#32 := by
    rw [h14w]; intro h; apply hc0'
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp at this
    rw [Nat.mod_eq_of_lt (by have := c0.isLt; omega)] at this
    simpa using this
  have hne1 : Silmaril.X86.Ext.Cond.eval (subD (BitVec.setWidth 32 (w.m.core.read .r14)) 45#32) .ne = some true := by
    rw [eval_subD]; simp [Silmaril.X86.Ext.Cond.afterCmp, hx14]
  have hne2 : Silmaril.X86.Ext.Cond.eval (@Silmaril.X86.Ext.AluOp.flagsN 32 Silmaril.X86.AluOp.sub
      (BitVec.setWidth 32 (w.m.core.read .r14)) 45#32) .ne = some true := hne1
  refine must_listed (o := 54) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (by simp only [hrw, ripadd]; exact hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3]; have := hKout x (Or.inl hx); omega)).2.digestFile (by simp only [hrw, ripadd]) ?_
  xstep [hrw]
  refine must_listed (o := 56) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 60) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by rw [ripadd]) ?_
  xstep [hne1, hne2]
  -- `*missing = false`
  have hregs : ∀ acc a len, (storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8
      (w.m.core.read .rax)).Permitted acc a len ↔ s.m.memory.Permitted acc a len := by
    intro acc a len
    rw [storeMem_permitted, hmw, storeMem_permitted, hmv, storeMem_permitted]
    simp only [Memory.Permitted, Memory.checkSpan, Memory.permits, hP.regs]
  refine must_listed (o := 67) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by rw [ripadd]) ?_
  rw [exec_storeb _ _ _ _ _ (by
    show (storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8 (w.m.core.read .rax)).Permitted
      .write (w.m.core.read .r12).toNat 1
    rw [hregs, h12w, hP.r12]; exact hmiss), WP_ok]
  -- the frame after the four stores
  have hsv := sv6_bound s
  have hsvb : ∀ q ∈ sv6 s, q.1 ≤ 48 := fun q hq => (hsv q hq).1
  have hA1 : A1.toNat = (s.m.core.read .rsp).toNat - 208 := a1
  let st1 : PState := ⟨⟨u.m.core, storeMem u.m.memory A1 8 (u.m.core.read .rdi)⟩, u.g⟩
  have hB1 : BodyX W (ShaMemCD b lb kb) s st1 216 1024 (sv6 s) (MX s) :=
    BodyX.store hMk hB (by decide) hsvb (by rw [hA1]; omega) (by rw [hA1]; omega) rfl rfl rfl rfl
  have hB2 : BodyX W (ShaMemCD b lb kb) s w 216 1024 (sv6 s) (MX s) :=
    BodyX.store hMk hB1 (by decide) hsvb (a := v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32)
      (v := v.m.core.read .rsi) (k := 8) (by rw [a2]; omega) (by rw [a2]; omega) (by rw [hmw, hmv])
      (by rw [hspw]) (by rw [hfsw]) (by rw [hgw])
  let st3 : PState := ⟨⟨w.m.core, storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8
    (w.m.core.read .rax)⟩, w.g⟩
  have hB3 : BodyX W (ShaMemCD b lb kb) s st3 216 1024 (sv6 s) (MX s) :=
    BodyX.store hMk hB2 (by decide) hsvb (by rw [a3']; omega) (by rw [a3']; omega) rfl rfl rfl rfl
  have hB4 : BodyX W (ShaMemCD b lb kb) s ⟨⟨w.m.core, storeMem st3.m.memory (s.m.core.read .rdx) 1
      (BitVec.setWidth 64 0#8)⟩, w.g⟩ 216 1024 (sv6 s) (MX s) :=
    BodyX.storeX hMk hB3 (sv6_bound8 s) (fun x h1 h2 => by
      have hd : DX s x := Or.inl ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, (hX x hd).1, Or.inr (hX x hd).2⟩) rfl rfl rfl rfl
  have hr12 : w.m.core.read .r12 = s.m.core.read .rdx := by rw [h12w, hP.r12]
  -- reading back the slots
  have hrA1 : u.m.memory.Permitted .read A1.toNat 8 := by rw [hA1]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hrA2 : v.m.memory.Permitted .read (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat 8 := by
    rw [a2, hmv, storeMem_permitted]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hrA3 : w.m.memory.Permitted .read (w.m.core.read .rbp + 18446744073709551560#64).toNat 8 := by
    rw [a3', hmw, storeMem_permitted, hmv, storeMem_permitted]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have kM4 : ∀ {P : Nat → Prop}, (∀ x, P x → x < (s.m.core.read .rdx).toNat ∨ (s.m.core.read .rdx).toNat + 1 ≤ x) →
      Keeps P st3.m.memory (storeMem st3.m.memory (s.m.core.read .rdx) 1 (BitVec.setWidth 64 0#8)) :=
    fun hP => storeMem_keeps hP
  have hrdx : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat :=
    (hX _ (Or.inl ⟨le_refl _, by omega⟩)).2
  refine must_gen (fun x => DigMid E W b lb kb s x g ∧ x.m.core.rip = b + 0x6a88#64 ∧
      BitVec.setWidth 32 (x.m.core.read .r14) ≠ 0#32) ?_ ?_
  · refine ⟨⟨hB4.of_eq (by simp [st3, hr12]) (by simp [hspw, hB.rsp]) (by simp [hfsw]) (by simp [hgw]),
      by simp [hbpw, hP.rbp], by simp [hr12], ?_, ?_, ?_, ?_, ?_, by simp [hgw, hP.g],
      by simp only [storeMem]; rw [hmw, hmv]; simp only [storeMem]; exact hP.regs⟩, by simp [ripadd], ?_⟩
    · show (storeMem _ _ 1 _).readBytes _ 8 = _
      rw [storeMem_read_ne (by simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
          not_false_eq_true, st_regs_apply, hr12]; omega),
        storeMem_read_ne (by rw [a3']; omega), hmw, storeMem_read_ne (by rw [a2]; omega), hmv, ← hA1]
      rw [storeMem_read8 hrA1, hP.rdi]
    · show (storeMem _ _ 1 _).readBytes _ 8 = _
      rw [storeMem_read_ne (by simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
          not_false_eq_true, st_regs_apply, hr12]; omega),
        storeMem_read_ne (by rw [a3']; omega), hmw, ← a2]
      rw [storeMem_read8 hrA2, hsiv, hP.rsi]
    · show (storeMem _ _ 1 _).readBytes _ 8 = _
      rw [storeMem_read_ne (by simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
          not_false_eq_true, st_regs_apply, hr12]; omega),
        ← a3']
      rw [storeMem_read8 hrA3, haxw]
    · show (storeMem _ _ 1 _).readBytes _ 1 = _
      simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, st_regs_apply, hr12]
      rw [storeMem_read (by
        rw [storeMem_permitted, hmw, storeMem_permitted, hmv, storeMem_permitted]
        simp only [Memory.Permitted, Memory.checkSpan, Memory.permits, hP.regs]
        exact hmissr)]
      rfl
    · intro a ha
      have hk : Keeps (fun x => x < E.S.lo) s.m.memory
          (storeMem (storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8 (w.m.core.read .rax))
            (s.m.core.read .rdx) 1 (BitVec.setWidth 64 0#8)) := by
        have h2 : Keeps (fun x => x < E.S.lo) s.m.memory w.m.memory := by
          rw [hmw]; exact (hkS.mono fun x hx => by omega).trans (hk2.mono fun x hx => by omega)
        exact (h2.trans (storeMem_keeps fun x hx => by rw [a3']; omega)).trans (storeMem_keeps fun x hx => by omega)
      have := hk a ha
      simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, st_regs_apply, hr12]
      exact ⟨this.1, this.2⟩
    · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same, Silmaril.X86.Ext.AluOp.resultN]
      intro h; apply hx14
      have := congrArg (· + 45#32) h
      simpa using this
  rintro x ⟨hM, hrx, h14x⟩
  exact k x hM hrx h14x

end Silmaril.Elf.Link.Dyn.Sha256sum
