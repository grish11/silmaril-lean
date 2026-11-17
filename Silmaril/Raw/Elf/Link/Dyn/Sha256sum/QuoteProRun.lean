module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteProB

/-! # GNU `sha256sum`: `Task.quotePro`, the run from `0x6720` to the loop head

* `quoteProA`: `0x6720` → `__errno_location` → `0x673d` → `0x681c` (`QPA`);
* `quoteProB`: `0x681c` → `0x4f50` → `__ctype_get_mb_cur_max` → `0x4fad` → `0x4fcd` → `0x588a`
  → `0x5860` → `0x50b8` → the loop head `0x50c0` (`QLoop` at `i = 0`);
* **`task_quotePro`**.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

set_option linter.unusedSimpArgs false

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams

theorem room_storeMem {W : World} {M : Memory} {a : Word} {k : Nat} {v R : Word} {n : Nat} :
    Room W (storeMem M a k v) R n ↔ Room W M R n := Iff.rfl

theorem loadN_hitR {W : World} {M : Memory} {R v : Word} {d k : Nat}
    (hroom : Room W (storeMem M (R - BitVec.ofNat 64 d) k v) R 2048) (hd : d ≤ 2048) (hk : k ≤ d + 8)
    (hv : v.toNat < 2 ^ (8 * k)) : loadN (storeMem M (R - BitVec.ofNat 64 d) k v) (R - BitVec.ofNat 64 d) k = some v :=
  loadN_storeMem_same (room_permR hroom (Or.inl rfl) hd hk) hv

theorem loadN_subR {W : World} {M : Memory} {R v : Word} {d e k j n : Nat}
    (hroom : Room W (storeMem M (R - BitVec.ofNat 64 d) k v) R 2048) (hd : d ≤ 2048) (hk : k ≤ d + 8)
    (hj : e + j = d) (hjk : j < k) (hjn : j + n ≤ k) :
    loadN (storeMem M (R - BitVec.ofNat 64 d) k v) (R - BitVec.ofNat 64 e) n =
      some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (((Silmaril.X86.Ext.leBytes v k).drop j).take n))) := by
  have h4 := hroom.1
  have := room_permR hroom (Or.inl rfl) hd hk
  rw [bsub_toNat (by omega)] at this
  have e' : e = d - j := by omega
  subst e'
  exact loadN_storeR (by omega) this hjk hjn (by omega)

/-- A load from a chain of stores below `R`: drop the stores it misses, rewrite with the given
equations, then read the store it hits. -/
syntax "ldq" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ldq [$ls,*]) => `(tactic| (
      simp (disch := first | omega | decide) only [loadN_stR, pushMem_eq, bsub_sub, Nat.reduceAdd, $ls,*]
      try (rw [loadN_hitR (by simp only [room_storeMem]; assumption) (by omega) (by omega)
        (by first | decide | exact BitVec.isLt _ | assumption | (simp only [Nat.reduceMul]; assumption))])))

/-- A chain of stores into the stack page down to a base memory keeps `OutStk`. -/
syntax "keeps_out'" : tactic
macro_rules
  | `(tactic| keeps_out') => `(tactic|
      ((repeat (first | exact Keeps.refl _ _ | (refine keeps_storeMem_right ?_ ?_; pick_goal 2)))
       all_goals (intro x hx; unfold OutStk at hx; rw [bsub_toNat (by omega)]; omega)))

/-- The state at `0x681c` (after `__errno_location` and `nslots > 0`). -/
structure QPA (E : Env) (W : World) (b : Word) (s : PState) (gv ev : Word) (c : PState) : Prop where
  rip : c.m.core.rip = b + 0x681c#64
  rsp : c.m.core.read .rsp = s.m.core.read .rsp - 0xb8#64
  rbp : c.m.core.read .rbp = s.m.core.read .rsp - 0x58#64
  r12 : c.m.core.read .r12 = s.m.core.read .rsp - 0x48#64
  r15 : c.m.core.read .r15 = b + 0xa020#64
  rbx : c.m.core.read .rbx = E.errnoA
  fs : c.m.core.fsBase = s.m.core.fsBase
  g : c.g = s.g
  F : QF E W b s c.m.memory
  m8 : loadN c.m.memory (s.m.core.read .rsp - 8#64) 8 = some (s.m.core.read .rbp)
  m10 : loadN c.m.memory (s.m.core.read .rsp - 0x10#64) 8 = some gv
  m3c : loadN c.m.memory (s.m.core.read .rsp - 0x3c#64) 4 = some 0x04000000#64
  m38 : loadN c.m.memory (s.m.core.read .rsp - 0x38#64) 4 = some 0#64
  m34 : loadN c.m.memory (s.m.core.read .rsp - 0x34#64) 4 = some 0#64
  m48 : loadN c.m.memory (s.m.core.read .rsp - 0x48#64) 4 = some 3#64
  m44 : loadN c.m.memory (s.m.core.read .rsp - 0x44#64) 4 = some 0#64
  m20 : loadN c.m.memory (s.m.core.read .rsp - 0x20#64) 8 = some 0#64
  m18 : loadN c.m.memory (s.m.core.read .rsp - 0x18#64) 8 = some 0#64
  m50 : loadN c.m.memory (s.m.core.read .rsp - 0x50#64) 8 = some (b + 0x6994#64)
  m58 : loadN c.m.memory (s.m.core.read .rsp - 0x58#64) 8 = some (s.m.core.read .rsp - 8#64)
  m60 : loadN c.m.memory (s.m.core.read .rsp - 0x60#64) 8 = some (s.m.core.read .r15)
  m68 : loadN c.m.memory (s.m.core.read .rsp - 0x68#64) 8 = some (s.m.core.read .r14)
  m70 : loadN c.m.memory (s.m.core.read .rsp - 0x70#64) 8 = some (s.m.core.read .r13)
  m78 : loadN c.m.memory (s.m.core.read .rsp - 0x78#64) 8 = some (s.m.core.read .r12)
  m80 : loadN c.m.memory (s.m.core.read .rsp - 0x80#64) 8 = some (s.m.core.read .rbx)
  m90 : loadN c.m.memory (s.m.core.read .rsp - 0x90#64) 8 = some (s.m.core.read .rdi)
  m94 : loadN c.m.memory (s.m.core.read .rsp - 0x94#64) 4 = some ev
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some gv
  ebytes : s.m.memory.readBytes E.errnoA.toNat 4 = some (Silmaril.X86.Ext.leBytes ev 4)
  ecell : ErrnoCell E W s.m.memory
  evlt : ev.toNat < 2 ^ 32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`0x6720` → `0x681c`**. -/
theorem quoteProA {E : Env} {W : World} {b lb : Word} {Q : PState → Prop} {s u : PState} {p : List Byte}
    (hE : QEntry E W b lb s p) (hA : QAfter b s u)
    (k : ∀ c gv ev, QPA E W b s gv ev c → MustQ W Q c) : MustQ W Q u := by
  obtain ⟨gv, hgv, hmem⟩ := hA.mem
  have hroom := hE.room
  generalize hR : s.m.core.read .rsp = R at hroom hmem k
  have h4 := hroom.1
  have hal : R.toNat % 16 = 8 := by rw [← hR]; exact hE.abi.aligned
  have I := hE.imps.img
  have hb := hE.imps.hb
  have hd : u.g.done = none := by rw [hA.g]; exact hE.done
  have hsp : u.m.core.read .rsp = R - 0x50#64 := by rw [hA.rsp, hR]
  have hmem' : u.m.memory = storeMem (storeMem (storeMem (storeMem (storeMem (storeMem (storeMem s.m.memory
      (R - 8#64) 8 (s.m.core.read .rbp)) (R - 0x10#64) 8 gv) (R - 0x48#64) 8 3#64) (R - 0x40#64) 16
      0x0400000000000000#64) (R - 0x30#64) 16 0#64) (R - 0x20#64) 16 0#64) (R - 0x50#64) 8 (b + 0x6994#64) := by
    rw [hmem, qproMem, pushMem_eq, bsub_sub]
  have hFu : QF E W b s u.m.memory := by
    rw [hmem']; exact QF.stores hE (QF.refl _ _ _ _) (by rw [hR]; keeps_out) rfl
  have hRu : Room W u.m.memory R 2048 := by rw [hmem']; exact hroom
  have hC6 : ∀ m, QF E W b s m → QC W b m 0x6614 quoteX6Text := fun m hF =>
    (hF.shaRO hE).qc I hb (by omega) (by have : quoteX6Text.length = 326 := (by decide); omega) (by decide)
      quoteX6_plain
  have hRm : ∀ m, QF E W b s m → Room W m R 2048 := fun m hF => by
    have := hF.room hE.room; rwa [hR] at this
  have hubp : u.m.core.read .rbp = R - 8#64 := by rw [hA.rbp, hR]
  have husi : u.m.core.read .rsi = R - 0x48#64 := by rw [hA.rsi, hR]
  have hur : ∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rsi → u.m.core.read r = s.m.core.read r := hA.other
  -- 0x6720
  refine qp6720 hd (hC6 _ hFu) hA.rip hRu hsp (fun c1 h1rip h1rsp h1rbp h1r12 h1o h1fs => ?_)
  generalize hM1 : storeMem _ _ _ _ = M1
  have hF1 : QF E W b s M1 := by rw [← hM1]; exact QF.stores hE hFu (by rw [hR]; keeps_out) rfl
  -- __errno_location
  refine qpErrno (v := ⟨⟨c1, M1⟩, u.g⟩) hd I hb hE.imps.lz (hF1.shaRO hE) hE.imps.errno h1rip (hRm _ hF1)
    h1rsp hal (fun t ht => ?_)
  obtain ⟨hL, htg, hO, hrax, -, hek, hcell⟩ := ht
  have hce : (callEntry ⟨⟨c1, M1⟩, u.g⟩ (lb + 0x2a6e0#64) (b + 0x673d#64)).m.memory =
      storeMem M1 (R - 0xc0#64) 8 (b + 0x673d#64) := by
    simp only [callEntry_mem]; rw [pushMem_eq, h1rsp, bsub_sub]
  have hcsp : (callEntry ⟨⟨c1, M1⟩, u.g⟩ (lb + 0x2a6e0#64) (b + 0x673d#64)).m.core.read .rsp = R - 0xc0#64 := by
    simp only [callEntry_rsp]; rw [h1rsp, bsub_sub]
  have hFce : QF E W b s (callEntry ⟨⟨c1, M1⟩, u.g⟩ (lb + 0x2a6e0#64) (b + 0x673d#64)).m.memory := by
    rw [hce]; exact QF.stores hE hF1 (by rw [hR]; keeps_out) rfl
  have hFt : QF E W b s t.m.memory := QF.call hFce (by rw [hcsp, hR, bsub_toNat (by omega)]; omega)
    (by rw [hcsp, hR, bsub_toNat (by omega)]; omega) hL hO hek
  have hpr : (callEntry ⟨⟨c1, M1⟩, u.g⟩ (lb + 0x2a6e0#64) (b + 0x673d#64)).m.memory.readBytes
      ((callEntry ⟨⟨c1, M1⟩, u.g⟩ (lb + 0x2a6e0#64) (b + 0x673d#64)).m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x673d#64]) := by
    simp only [callEntry_mem, callEntry_rsp]
    exact pushMem_read (by rw [h1rsp, bsub_sub]; exact room_permR (hRm _ hF1) (Or.inl rfl) (by omega) (by omega))
      (by rw [h1rsp, bsub_sub]; exact room_permR (hRm _ hF1) (Or.inr rfl) (by omega) (by omega))
  have htrip : t.m.core.rip = b + 0x673d#64 := by
    rw [hL.1.1.pc]; exact Silmaril.Elf.Link.Dyn.Hello.retOf_of hpr
  have htsp : t.m.core.read .rsp = R - 0xb8#64 := by rw [hL.1.1.stack, hcsp]; bv_omega
  have htcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = c1.read r := fun r hr => by
    rw [hL.1.1.calleeSaved r hr]
    exact callEntry_read _ _ _ (fun h => by subst h; exact Silmaril.X86.sysv64_rsp_not_calleeSaved hr)
  have htbp : t.m.core.read .rbp = R - 0x58#64 := (htcs .rbp (by decide)).trans h1rbp
  have hkT : ∀ X n, X ≤ 0xc0 → n ≤ X → loadN t.m.memory (R - BitVec.ofNat 64 X) n =
      loadN (storeMem M1 (R - 0xc0#64) 8 (b + 0x673d#64)) (R - BitVec.ofNat 64 X) n := by
    intro X n h1 h2
    rw [← hce]
    exact hL.1.2.loadN fun j hj => ⟨Or.inr (by rw [hcsp, bsub_toNat (by omega), bsub_toNat (by omega)]; omega),
      fun h => h⟩
  obtain ⟨ev, hev0⟩ := hE.errnoRd
  have hev : loadN t.m.memory E.errnoA 4 = some ev := by
    rw [hFt.errno.loadN fun j hj => ⟨by omega, by omega⟩]; exact hev0
  have hdt : t.m.core.fsBase = s.m.core.fsBase := by
    rw [hL.2.1]; show c1.fsBase = _; rw [h1fs, hA.fs]
  have htg' : t.g = s.g := by rw [htg]; exact hA.g
  -- 0x673d
  refine qp673d (v := t) (ea := E.errnoA) (ev := ev) (by rw [htg']; exact hE.done) (hC6 _ hFt) htrip
    (hRm _ hFt) htbp hrax (hFt.slots hE) hev (fun c2 h2rip h2rbx h2r15 h2o h2fs => ?_)
  have hF2 : QF E W b s (storeMem t.m.memory (R - 0x94#64) 4 ev) :=
    QF.stores hE hFt (by rw [hR]; keeps_out) rfl
  have hRt := hRm _ hFt
  have hRM1 := hRm _ hF1
  have hlt : ev.toNat < 2 ^ 32 := loadN_lt hev0
  have hr1 : ∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .r12 → c1.read r = u.m.core.read r := h1o
  refine k _ gv ev ⟨h2rip, ?_, ?_, ?_, h2r15, h2rbx, ?_, htg', hF2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgv, readBytes_of_loadN' hev0 (by omega),
    ⟨(hFt.errno.permitted fun j hj => ⟨by omega, by omega⟩).1 hcell.1,
      (hFt.errno.permitted fun j hj => ⟨by omega, by omega⟩).1 hcell.2.1, hcell.2.2⟩, hlt⟩
  · rw [h2o .rsp (by decide) (by decide) (by decide) (by decide), htsp, hR]
  · rw [h2o .rbp (by decide) (by decide) (by decide) (by decide), htbp, hR]
  · rw [h2o .r12 (by decide) (by decide) (by decide) (by decide), htcs .r12 (by decide), h1r12, husi, hR]
  · rw [h2fs, hdt]
  all_goals rw [hR]
  all_goals ldq [hkT, ← hM1, hmem', hubp, husi, hur]
  all_goals first
    | (rw [loadN_subR (j := 0) (by simp only [room_storeMem]; assumption) (by omega) (by omega) (by omega)
        (by omega) (by omega)]; rfl)
    | (rw [loadN_subR (j := 4) (by simp only [room_storeMem]; assumption) (by omega) (by omega) (by omega)
        (by omega) (by omega)]; rfl)
    | (rw [loadN_subR (j := 8) (by simp only [room_storeMem]; assumption) (by omega) (by omega) (by omega)
        (by omega) (by omega)]; rfl)
    | (rw [loadN_subR (j := 12) (by simp only [room_storeMem]; assumption) (by omega) (by omega) (by omega)
        (by omega) (by omega)]; rfl)

theorem readBytes_zeroQ {m : Memory} {a : Nat} (h : a < 2 ^ 64) : m.readBytes a 0 = some [] := by
  simp [Memory.readBytes, Memory.readWith, Memory.checkSpan, Memory.readBacking,
    Silmaril.Process.addressLimit]
  omega

/-- The jump-table entry of style 3 (`0x7f48 + 4·3`): `0x588a - 0x7f48`. -/
def jt3 : List Byte := ([0x42, 0xd9, 0xff, 0xff] : List Nat).map (BitVec.ofNat 8)

theorem jt3_plain : plainOk shaFile shaRoPh shaSlots 0x7f54 jt3 = true := by decide +kernel

theorem ShaRO.jtab {b lb : Word} {m : Memory} (h : ShaRO b lb m) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    loadN m (b + 0x7f54#64) 4 = some 0xffffd942#64 := by
  have := h.readRo hb (v := 0x7f54) (l := jt3) (by omega) (by decide) (by decide) jt3_plain
  simp only [loadN, show jt3.length = 4 from rfl] at this ⊢
  rw [this]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`0x681c` → the loop head**. -/
theorem quoteProB {E : Env} {W : World} {b lb : Word} {Q : PState → Prop} {s c : PState} {p : List Byte}
    {gv ev : Word} (hE : QEntry E W b lb s p) (hP : QPA E W b s gv ev c)
    (k : ∀ w, QLoop E W b s p gv ev 0 w → MustQ W Q w) : MustQ W Q c := by
  have hroom := hE.room
  have hPF := hP.F
  have hPg := hP.g
  have hPfs := hP.fs
  have hm8 := hP.m8
  have hm10 := hP.m10
  have hm3c := hP.m3c
  have hm38 := hP.m38
  have hm34 := hP.m34
  have hm48 := hP.m48
  have hm44 := hP.m44
  have hm20 := hP.m20
  have hm18 := hP.m18
  have hm50 := hP.m50
  have hm58 := hP.m58
  have hm60 := hP.m60
  have hm68 := hP.m68
  have hm70 := hP.m70
  have hm78 := hP.m78
  have hm80 := hP.m80
  have hm90 := hP.m90
  have hm94 := hP.m94
  have hcrsp := hP.rsp
  have hcrbp := hP.rbp
  have hcr12 := hP.r12
  generalize hR : s.m.core.read .rsp = R at hroom hm8 hm10 hm3c hm38 hm34 hm48 hm44 hm20 hm18 hm50 hm58 hm60 hm68 hm70 hm78 hm80 hm90 hm94 hcrsp hcrbp hcr12
  have h4 := hroom.1
  have hal : R.toNat % 16 = 8 := by rw [← hR]; exact hE.abi.aligned
  have I := hE.imps.img
  have hb := hE.imps.hb
  have hRm : ∀ m, QF E W b s m → Room W m R 2048 := fun m hF => by
    have := hF.room hE.room; rwa [hR] at this
  have hQC : ∀ m, QF E W b s m → ∀ {cb : Nat} {code : List Byte}, 0x2000 ≤ cb →
      cb + code.length ≤ 0x2000 + 0x4d51 → 0 < code.length → plainOk shaFile shaTextPh shaSlots cb code = true →
      QC W b m cb code := fun m hF _ _ h1 h2 h3 h4 => (hF.shaRO hE).qc I hb h1 h2 h3 h4
  have l0 : quoteX0Text.length = 496 := by decide
  have l2 : quoteX2Text.length = 75 := by decide
  have l7 : quoteX7Text.length = 393 := by decide
  have hd : c.g.done = none := by rw [hPg]; exact hE.done
  have hRc := hRm _ hPF
  -- 0x681c
  refine qp681c (nm := s.m.core.read .rdi) hd (hQC _ hPF (by omega) (by omega) (by omega) quoteX7_plain) hP.rip
    hRc hcrbp hcrsp hcr12 hP.r15 (hPF.slots hE) hm44 hm48 hm90 hm18 hm20
    (fun c1 h1rip h1rsp h1rdi h1rsi h1rdx h1rcx h1r8 h1r9 h1r13 h1r14 h1o h1fs => ?_)
  generalize hM2 : storeMem _ _ _ _ = M2
  have hF2 : QF E W b s M2 := by rw [← hM2]; exact QF.stores hE hPF (by rw [hR]; keeps_out') rfl
  have hR2 := hRm _ hF2
  -- call 0x4f50
  refine qpCall (c := ⟨⟨c1, M2⟩, c.g⟩) hd (hQC _ hF2 (by omega) (by omega) (by omega) quoteX7_plain) h1rip
    (by show M2.Permitted _ _ _; rw [h1rsp, bsub_sub]; exact room_permR hR2 (Or.inr rfl) (by omega) (by omega))
    (fun c2 h2rip h2rsp h2o h2fs => ?_)
  have hM3 : pushMem M2 (c1.read .rsp) (b + 0x6859#64) = storeMem M2 (R - 0xd0#64) 8 (b + 0x6859#64) := by
    rw [pushMem_eq, h1rsp, bsub_sub]
  rw [show (⟨⟨c1, M2⟩, c.g⟩ : PState).m.memory = M2 from rfl, hM3]
  have hF3 : QF E W b s (storeMem M2 (R - 0xd0#64) 8 (b + 0x6859#64)) := QF.stores hE hF2 (by rw [hR]; keeps_out') rfl
  have hR3 := hRm _ hF3
  have hc2 : ∀ r, r ≠ .rsp → c2.read r = c1.read r := h2o
  have hc1 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsp → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 →
      r ≠ .r13 → r ≠ .r14 → c1.read r = c.m.core.read r := h1o
  have hfs2 : c2.fsBase = s.m.core.fsBase := by rw [h2fs]; show c1.fsBase = _; rw [h1fs, hPfs]
  -- 0x4f50
  refine qp4f50 (c := ⟨⟨c2, _⟩, c.g⟩) (ea := E.errnoA) (g := gv) hd
    (hQC _ hF3 (by omega) (by omega) (by omega) quoteX0_plain) h2rip hR3
    (by show c2.read .rsp = _; rw [h2rsp, h1rsp, bsub_sub])
    (by show c2.read .rbp = _; rw [hc2 _ (by decide), hc1 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcrbp])
    (by show c2.read .r15 = _; rw [hc2 _ (by decide), hc1 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hP.r15])
    (by show c2.read .r14 = _; rw [hc2 _ (by decide), h1r14])
    (by show c2.read .r13 = _; rw [hc2 _ (by decide), h1r13])
    (by show c2.read .r12 = _; rw [hc2 _ (by decide), hc1 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcr12])
    (by show c2.read .rbx = _; rw [hc2 _ (by decide), hc1 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hP.rbx])
    (by show c2.read .rdi = _; rw [hc2 _ (by decide), h1rdi])
    (by show c2.read .rsi = _; rw [hc2 _ (by decide), h1rsi])
    (by show c2.read .rdx = _; rw [hc2 _ (by decide), h1rdx])
    (by show c2.read .rcx = _; rw [hc2 _ (by decide), h1rcx])
    (by show c2.read .r8 = _; rw [hc2 _ (by decide), h1r8])
    (by show c2.read .r9 = _; rw [hc2 _ (by decide), h1r9])
    (by show loadN _ _ _ = _; ldq [← hM2])
    (by show loadN _ _ _ = _; ldq [← hM2])
    (fun m' hk => by
      show loadN m' (c2.fsBase + 0x28#64) 8 = _
      rw [hfs2, hk.loadN fun j hj => ?_]
      · rw [(hF3.keepK hE.room).loadN fun j hj => ⟨hE.guardk j hj, hE.guardq j hj⟩]; exact hP.guard
      · have hk1 := hE.guardk j hj
        have hr := hroom.2.2 ((s.m.core.fsBase + 0x28#64).toNat + j)
        unfold OutStk
        by_contra hc
        exact (hr (by omega) (by omega)).2.2 hk1)
    (fun c3 h3rip h3rsp h3rbp h3r9 h3r11 h3r14 h3fs => ?_)
  generalize hM4 : storeMem _ _ _ _ = M4
  have hF4 : QF E W b s M4 := by rw [← hM4]; exact QF.stores hE hF3 (by rw [hR]; keeps_out') rfl
  have hR4 := hRm _ hF4
  -- __ctype_get_mb_cur_max
  refine qpMb (v := ⟨⟨c3, M4⟩, c.g⟩) hd I hb hE.imps.lz (hF4.shaRO hE) hE.imps.mbcur h3rip hR4 h3rsp hal
    (fun t ht => ?_)
  obtain ⟨hL, htg, hO, hrax, hek⟩ := ht
  have hce : (callEntry ⟨⟨c3, M4⟩, c.g⟩ (lb + 0x39480#64) (b + 0x4fad#64)).m.memory =
      storeMem M4 (R - 0x1d0#64) 8 (b + 0x4fad#64) := by
    simp only [callEntry_mem]; rw [pushMem_eq, h3rsp, bsub_sub]
  have hcsp : (callEntry ⟨⟨c3, M4⟩, c.g⟩ (lb + 0x39480#64) (b + 0x4fad#64)).m.core.read .rsp = R - 0x1d0#64 := by
    simp only [callEntry_rsp]; rw [h3rsp, bsub_sub]
  have hFce : QF E W b s (callEntry ⟨⟨c3, M4⟩, c.g⟩ (lb + 0x39480#64) (b + 0x4fad#64)).m.memory := by
    rw [hce]; exact QF.stores hE hF4 (by rw [hR]; keeps_out') rfl
  have hFt : QF E W b s t.m.memory := QF.call hFce (by rw [hcsp, hR, bsub_toNat (by omega)]; omega)
    (by rw [hcsp, hR, bsub_toNat (by omega)]; omega) hL hO hek
  have hRt := hRm _ hFt
  have hpr : (callEntry ⟨⟨c3, M4⟩, c.g⟩ (lb + 0x39480#64) (b + 0x4fad#64)).m.memory.readBytes
      ((callEntry ⟨⟨c3, M4⟩, c.g⟩ (lb + 0x39480#64) (b + 0x4fad#64)).m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x4fad#64]) := by
    simp only [callEntry_mem, callEntry_rsp]
    exact pushMem_read (by rw [h3rsp, bsub_sub]; exact room_permR hR4 (Or.inl rfl) (by omega) (by omega))
      (by rw [h3rsp, bsub_sub]; exact room_permR hR4 (Or.inr rfl) (by omega) (by omega))
  have htrip : t.m.core.rip = b + 0x4fad#64 := by
    rw [hL.1.1.pc]; exact Silmaril.Elf.Link.Dyn.Hello.retOf_of hpr
  have htsp : t.m.core.read .rsp = R - 0x1c8#64 := by rw [hL.1.1.stack, hcsp]; bv_omega
  have htcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = c3.read r := fun r hr => by
    rw [hL.1.1.calleeSaved r hr]
    exact callEntry_read _ _ _ (fun h => by subst h; exact Silmaril.X86.sysv64_rsp_not_calleeSaved hr)
  have htbp : t.m.core.read .rbp = R - 0xd8#64 := (htcs .rbp (by decide)).trans h3rbp
  have htr14 : t.m.core.read .r14 = 0xffffffffffffffff#64 := (htcs .r14 (by decide)).trans h3r14
  have hkT : ∀ X n, X ≤ 0x1d0 → n ≤ X → loadN t.m.memory (R - BitVec.ofNat 64 X) n =
      loadN (storeMem M4 (R - 0x1d0#64) 8 (b + 0x4fad#64)) (R - BitVec.ofNat 64 X) n := by
    intro X n h1 h2
    rw [← hce]
    exact hL.1.2.loadN fun j hj => ⟨Or.inr (by rw [hcsp, bsub_toNat (by omega), bsub_toNat (by omega)]; omega),
      fun h => h⟩
  have hdt : t.m.core.fsBase = s.m.core.fsBase := by
    rw [hL.2.1]; show c3.fsBase = _; rw [h3fs]; exact hfs2
  have htg' : t.g = c.g := htg
  have hdt' : t.g.done = none := by rw [htg']; exact hd
  -- 0x4fad
  refine qp4fad (c := t) hdt' (hQC _ hFt (by omega) (by omega) (by omega) quoteX0_plain) htrip hRt htbp hrax
    (by ldq [hkT, ← hM4]) (by ldq [hkT, ← hM4]) (fun c5 h5rip h5rax h5o h5fs => ?_)
  have hF5 : QF E W b s (storeMem (storeMem t.m.memory (R - 0x1a8#64) 8 1#64) (R - 0x135#64) 1 0#64) :=
    QF.stores hE hFt (by rw [hR]; keeps_out') rfl
  have hR5 := hRm _ hF5
  have hc5 : ∀ r, r ≠ .rax → r ≠ .rbx → c5.read r = t.m.core.read r := h5o
  -- 0x4fcd
  refine qp4fcd (c := ⟨⟨c5, _⟩, t.g⟩) hdt' (hQC _ hF5 (by omega) (by omega) (by omega) quoteX0_plain) h5rip hR5
    (by show c5.read .rbp = _; rw [hc5 _ (by decide) (by decide), htbp]) h5rax
    (by show loadN _ _ _ = _; ldq [hkT, ← hM4]) (by show loadN _ _ _ = _; ldq [hkT, ← hM4])
    ((hF5.shaRO hE).jtab hb) (fun c6 h6rip h6r9 h6r11 h6o h6fs => ?_)
  have hc6 : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .r9 → r ≠ .r11 → c6.read r = c5.read r := h6o
  -- 0x588a
  refine qp588a (c := ⟨⟨c6, _⟩, t.g⟩) hdt' (hQC _ hF5 (by omega) (by omega) (by omega) quoteX2_plain) h6rip hR5
    (by show c6.read .rbp = _; rw [hc6 _ (by decide) (by decide) (by decide) (by decide),
      hc5 _ (by decide) (by decide), htbp])
    (fun c7 M7 h7rip h7o h7fs hM7 => ?_)
  have hF7 : QF E W b s M7 := by rw [hM7]; exact QF.stores hE hF5 (by rw [hR]; keeps_out') rfl
  have hR7 := hRm _ hF7
  -- 0x5860
  refine qp5860 (c := ⟨⟨c7, M7⟩, t.g⟩) hdt' (hQC _ hF7 (by omega) (by omega) (by omega) quoteX2_plain) h7rip hR7
    (by show c7.read .rbp = _; rw [h7o, hc6 _ (by decide) (by decide) (by decide) (by decide),
      hc5 _ (by decide) (by decide), htbp])
    (fun c8 h8rip h8o h8fs => ?_)
  have hF8 : QF E W b s (storeMem (storeMem (storeMem (storeMem M7 (R - 0x150#64) 8 1#64) (R - 0x190#64) 8
      (b + 0x70d7#64)) (R - 0x130#64) 8 0#64) (R - 0x134#64) 4 2#64) :=
    QF.stores hE hF7 (by rw [hR]; keeps_out') rfl
  have hR8 := hRm _ hF8
  -- 0x50b8
  refine qp50b8 (c := ⟨⟨c8, _⟩, t.g⟩) hdt' (hQC _ hF8 (by omega) (by omega) (by omega) quoteX0_plain) h8rip
    (fun c9 h9rip h9rbx h9o h9fs => ?_)
  have hreg : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rsi → r ≠ .r9 → r ≠ .r11 → c9.read r = t.m.core.read r :=
    fun r h1 h2 h3 h4 h5 => by
      show c9.read r = _
      rw [h9o r h2]; show c8.read r = _
      rw [h8o r h1]; show c7.read r = _
      rw [h7o r, hc6 r h1 h3 h4 h5, hc5 r h1 h2]
  have h96 : ∀ r, r ≠ .rax → r ≠ .rbx → c9.read r = c6.read r := fun r h1 h2 => by
    show c9.read r = _
    rw [h9o r h2]; show c8.read r = _
    rw [h8o r h1]; show c7.read r = _
    rw [h7o r]
  refine k _ ⟨h9rip, ?_, ?_, h9rbx, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    readBytes_of_loadN' (show loadN _ (s.m.core.read .rsp - 0x94#64) 4 = some ev by
      rw [hR]; ldq [hkT, ← hM4, ← hM2, hM7, hm94]) (by omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [hR]; ldq [hkT, ← hM4, ← hM2, hM7],
    ⟨1#64, by rw [hR]; ldq [hkT, ← hM4, ← hM2, hM7]⟩,
    by simp only [List.take_zero]; exact readBytes_zeroQ (BitVec.isLt _),
    hF8, Nat.zero_le _, hP.guard, hP.ebytes, hP.ecell⟩
  · show c9.read .rsp = _; rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide), htsp, hR]
  · show c9.read .rbp = _; rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide), htbp, hR]
  · show c9.read .r9 = _; rw [h96 _ (by decide) (by decide), h6r9]
  · show c9.read .r11 = _; rw [h96 _ (by decide) (by decide), h6r11]
  · show c9.read .r14 = _; rw [hreg _ (by decide) (by decide) (by decide) (by decide) (by decide), htr14]
  · show c9.fsBase = _; rw [h9fs, h8fs, h7fs, h6fs, h5fs, hdt]
  · show t.g = _; rw [htg', hPg]
  all_goals rw [hR]
  all_goals ldq [hkT, ← hM4, ← hM2, hM7, hm8, hm10, hm3c, hm38, hm34, hm50, hm58, hm60, hm68, hm70, hm78, hm80]

/-- **`Task.quotePro`**. -/
theorem task_quotePro {E : Env} {W : World} {b lb : Word} : Task.quotePro E W b lb := by
  intro Q s u p hE _ hA kL
  exact quoteProA hE hA fun c gv ev hP => quoteProB hE hP fun w hw => kL w gv ev hw

end Silmaril.Elf.Link.Dyn.Sha256sum
