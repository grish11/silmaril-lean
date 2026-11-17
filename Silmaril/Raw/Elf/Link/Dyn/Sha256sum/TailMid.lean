module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailRun4
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintTask
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestStdin

/-! # GNU `sha256sum`, stdin tier: `main` from the call of `digest_file` to the end of the line

`0x2b81` → `0x2c8a`: `call digest_file` (`call2b81`), `digest_file ("-")` on standard input
(`task_digestStdin`), `test al` (`0x2b86`), and the result line (`task_printLine`).

`body_now`: after a local call whose callee returns (System V) keeping the caller's data
except some objects `F`, the caller's body continues from a base with the caller's entry
registers and the memory after the call (the history before the call is dropped; what the
caller still needs is carried by `Keeps` facts).
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
open Silmaril.Elf.Link.Dyn.Cert

/-- The call of `digest_file` at `0x2b81` (`call 0x6a40`). -/
def callDigestListing : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0x55, .ext8 (.base (.call 0x3eba#32)), 5)]

theorem callDigest_ok : listingOk mainAll2Text callDigestListing = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- `0x2b81`: `call digest_file`: the return address `0x2b86` pushed, control at `0x6a40`. -/
theorem call2b81 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b81#64)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8)
    (k : MustQ W Q (callEntry u (b + 0x6a40#64) (b + 0x2b86#64))) : MustQ W Q u := by
  refine must_listed (o := 0x55) callDigest_ok rfl hd (by rw [hrip]; exact sha_in' I hb (by decide))
    hMA.ld2 (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_call _ _ _ _ hw, WP_ok, hrip,
    show b + 0x2b81#64 + BitVec.ofNat 64 5 + BitVec.signExtend 64 0x3eba#32 = b + 0x6a40#64 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl,
    show b + 0x2b81#64 + BitVec.ofNat 64 5 = b + 0x2b86#64 by rw [BitVec.add_assoc]; rfl]
  exact k

/-- The base of a body continued after a call: the entry registers, the memory `m`. -/
def reb (s : PState) (m : Memory) : PState := ⟨⟨s.m.core, m⟩, s.g⟩

@[simp] theorem reb_core (s : PState) (m : Memory) : (reb s m).m.core = s.m.core := rfl
@[simp] theorem reb_mem (s : PState) (m : Memory) : (reb s m).m.memory = m := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- **The body after a local call** entered at `e = callEntry u f ret` whose callee returned in
`v` keeping the caller's data outside `F`, with the stack's permissions (below `e`'s stack
pointer, `PermKept`; of `F` inside the room, `hF`), the saved registers outside `F`, and the
image facts `M` of `v`'s memory. The body continues from `reb s v.m.memory`. -/
theorem body_now {W : World} {M : Memory → Prop} {s u v : PState} {fr n : Nat}
    {saved : List (Nat × Word)} (hB : Body W M s u fr n saved) (hfr : fr + 8 ≤ n) {sv : Nat}
    (hsv : ∀ p ∈ saved, 8 ≤ p.1 ∧ p.1 ≤ sv) (hsvf : sv ≤ fr) (hn : n + fr + 8 ≤ 0x80000) {f ret : Word} {F : Nat → Prop}
    (habi : AbiReturn (callEntry u f ret).m.core (callEntry u f ret).m.memory v.m.core)
    (hk : Keeps (fun a => (W.Kept a ∨ ((callEntry u f ret).m.core.read .rsp).toNat ≤ a) ∧ ¬ F a)
      (callEntry u f ret).m.memory v.m.memory)
    (hp : PermKept (callEntry u f ret) v.m.memory)
    (hF : ∀ a, F a → (s.m.core.read .rsp).toNat - n ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      ∀ acc, v.m.memory.permits acc a = u.m.memory.permits acc a)
    (hFs : ∀ a, F a → a + sv < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hM : M v.m.memory) (hfs : v.m.core.fsBase = u.m.core.fsBase) (hd : v.g.done = none) :
    Body W M (reb s v.m.memory) v fr n saved ∧ v.m.core.rip = ret ∧
      v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) := by
  have hroom := hB.room
  have hn1 := hroom.1
  have hn2 := hroom.2.1
  have eu : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by omega)
  have ee : ((callEntry u f ret).m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr - 8 := by
    rw [callEntry_rsp, sub_toNat (k := 8) (by omega) (by decide), eu]
  have hpr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by rw [sub_toNat (k := 8) (by omega) (by decide), eu]; omega)
      (by rw [sub_toNat (k := 8) (by omega) (by decide), eu]; omega)
  have hpw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by rw [sub_toNat (k := 8) (by omega) (by decide), eu]; omega)
      (by rw [sub_toNat (k := 8) (by omega) (by decide), eu]; omega)
  have hret : (callEntry u f ret).m.memory.readBytes ((callEntry u f ret).m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [ret]) := by
    rw [callEntry_rsp, callEntry_mem]; exact pushMem_read hpr hpw
  have hku : Keeps (fun a => (s.m.core.read .rsp).toNat - fr ≤ a) u.m.memory (callEntry u f ret).m.memory := by
    rw [callEntry_mem]
    exact pushMem_keeps fun x hx => Or.inr (by rw [sub_toNat (k := 8) (by omega) (by decide), eu]; omega)
  have hperm : ∀ a, (s.m.core.read .rsp).toNat - n ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      ∀ acc, v.m.memory.permits acc a = u.m.memory.permits acc a := by
    intro a h1 h2 acc
    by_cases hfa : F a
    · exact hF a hfa h1 h2 acc
    by_cases hlo : a < (s.m.core.read .rsp).toNat - fr - 8 + 8
    · rw [hp a (by rw [ee]; omega) (by rw [ee]; exact hlo) acc]; rfl
    · rw [(hk a ⟨Or.inr (by rw [ee]; omega), hfa⟩).2 acc]; rfl
  refine ⟨⟨?_, Keeps.refl _ _ |>.mono fun _ _ => trivial, ?_, hM, hfs.trans hB.fs, hd, ?_,
    fun _ _ _ _ => rfl⟩, ?_, ?_, ?_⟩
  · rw [habi.stack, callEntry_rsp, BitVec.sub_add_cancel]; exact hB.rsp
  · refine ⟨hn1, hn2, fun a h1 h2 => ?_⟩
    rw [hperm a h1 h2, hperm a h1 h2]
    exact hroom.2.2 a h1 h2
  · intro p hp'
    obtain ⟨hp1, hp2⟩ := hsv p hp'
    show v.m.memory.readBytes ((s.m.core.read .rsp).toNat - p.1) 8 = _
    rw [hk.readBytes (fun j hj => ⟨Or.inr (by rw [ee]; omega), fun hf => by
        rcases hFs _ hf with h | h <;> omega⟩),
      hku.readBytes (fun j hj => by omega)]
    exact hB.saved p hp'
  · rw [habi.pc]; exact Silmaril.Elf.Link.Dyn.Hello.retOf_of hret
  · rw [habi.stack, callEntry_rsp, BitVec.sub_add_cancel]
  · intro r hr
    rw [habi.calleeSaved r hr]
    exact callEntry_read _ _ _ (fun h => Silmaril.X86.sysv64_rsp_not_calleeSaved (h ▸ hr))

theorem low8_of_low32 {x : Word} (h : low32 x = 1#32) : x.setWidth 8 = 1#8 := by
  have := congrArg (BitVec.setWidth 8) h
  rw [low32, BitVec.setWidth_setWidth_of_le _ (by decide)] at this
  exact this

theorem m60_eq (sp : Word) : sp - 8#64 + 0xffffffffffffffa0#64 = sp - 8#64 - 0x60#64 := by
  rw [BitVec.sub_eq_add_neg (sp - 8#64)]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **From the call of `digest_file ("-")` to the end of the result line** (`0x2b81` →
`0x2c8a`), stdin tier: `digest_file` digests standard input (`task_digestStdin`), returns true,
and the result line `hex(SHA-256(data)) ++ "  -\n"` goes to `stdout` (`task_printLine`). -/
theorem tail_mid {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (D : StdinImps E R W b lb kb) (P : PrintImps E W b lb sc) (hPL : PutcLaw E) (hSD : StreamsDisj E)
    (hPA : PrivApart E W) {Q : PState → Prop} {sB v : PState} {sp : Word}
    (hspB : sB.m.core.read .rsp = sp)
    (hB : Body W (ShaMemAll b lb kb sr sc) sB v 328 4096 (sv6 sB)) (hMA : ShaMainAll b v.m.memory)
    (hrw : ShaRw b v.m.memory)
    (hrip : v.m.core.rip = b + 0x2b81#64) (hrbp : v.m.core.read .rbp = sp - 8#64)
    (hrdi : v.m.core.read .rdi = b + 0x716e#64) (hr12 : v.m.core.read .r12 = b + 0x716e#64)
    (hrsi : v.m.core.read .rsi = sp - 8#64 + 0xffffffffffffffa0#64)
    (hrbx : v.m.core.read .rbx = sp - 8#64 + 0xffffffffffffffa0#64)
    (hrdx : v.m.core.read .rdx = sp - 8#64 + 0xffffffffffffff58#64)
    (hr14 : v.m.core.read .r14 = b + 0x7238#64)
    (hlo : E.S.lo + 4096 ≤ sp.toNat) (hal : sp.toNat % 16 = 8)
    (hclr : loadN v.m.memory (b + 0x9f68#64) 8 = some (lb + 0x91400#64))
    {g Fi : Word} (hg : loadN v.m.memory (v.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((v.m.core.fsBase + 0x28#64).toNat + j))
    (hgHR : ∀ j, j < 8 → (v.m.core.fsBase + 0x28#64).toNat + j ≠ (b + 0xa160#64).toNat)
    (hvar : loadN v.m.memory (lb + 0x2056b0#64) 8 = some Fi)
    (hvark : ∀ j, j < 8 → W.Kept ((lb + 0x2056b0#64).toNat + j))
    (hvarHR : ∀ j, j < 8 → (lb + 0x2056b0#64).toNat + j ≠ (b + 0xa160#64).toNat) (hfi0 : Fi ≠ 0#64)
    {data : List Byte} (hin : E.S.file v.m.memory Fi (stdinSt data)) (hFo : Fi ≠ E.stdoutF)
    {sto : St} (hout : StdoutIs E v.m.memory sto) (hoe : sto.err = false)
    (hvars : StdVars E W lb v.m.memory) (hImgVar : ∀ a, ShaImg b a → ¬ VarR lb a)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64) (hrel : W.reliable = true)
    (htag : v.m.memory.readBytes (sp.toNat - 216) 1 = some [0#8])
    (hbin : v.m.memory.readBytes (sp.toNat - 208) 4 = some [0xff#8, 0xff#8, 0xff#8, 0xff#8])
    (hlen : loadN v.m.memory (b + 0xa178#64) 8 = some 0x40#64)
    (hres : InMain v.g ∧ v.g.allocs < E.maxAllocs ∧ v.g.heap + 0x8048 ≤ E.maxHeap)
    (k : ∀ x sR : PState, sR.m.core = sB.m.core → sR.g = sB.g →
      Body W (ShaMemAll b lb kb sr sc) sR x 328 4096 (sv6 sR) → ShaMainAll b x.m.memory →
      x.m.core.rip = b + 0x2c8a#64 →
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], x.m.core.read r = v.m.core.read r) →
      x.m.core.fsBase = v.m.core.fsBase →
      Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 0x68 ≤ a ∧ a < sp.toNat - 0x48) ∧
        a ≠ sp.toNat - 0xb0 ∧ a ≠ (b + 0xa160#64).toNat ∧ ¬ (sp.toNat - 256 ≤ a ∧ a < sp.toNat - 252) ∧
        a ≠ sp.toNat - 244) v.m.memory x.m.memory →
      x.m.memory.readBytes (b + 0xa160#64).toNat 1 = some [1#8] →
      (∃ st', E.S.file x.m.memory Fi st' ∧ st'.rd = [] ∧ st'.eof = false ∧ st'.err = false ∧
        st'.reading = true ∧ st'.fd = 0) →
      (∃ st', StdoutIs E x.m.memory st' ∧ st'.err = false ∧ st'.reading = sto.reading ∧
        x.g.out ++ st'.buf = v.g.out ++ sto.buf ++ stdinLine data) →
      x.g.jobs = v.g.jobs → x.g.atexit = v.g.atexit → x.g.done = none →
      (∀ f st', f ≠ Fi → f ≠ E.stdoutF → E.S.file v.m.memory f st' → E.S.file x.m.memory f st') →
      MustQ W Q x) : MustQ W Q v := by
  have I := D.dig.cl.img
  have hb := D.dig.cl.hb
  have hroom := hB.room
  rw [hspB] at hroom
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hvsp : v.m.core.read .rsp = sp - 328#64 := by rw [hB.rsp, hspB]
  have e328 : (v.m.core.read .rsp).toNat = sp.toNat - 328 := by
    rw [hvsp]; exact sub_toNat (k := 328) (by omega) (by decide)
  have e336 : (v.m.core.read .rsp - 8#64).toNat = sp.toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e328]; omega
  have hKroom : ∀ a, sp.toNat - 4096 ≤ a → a < sp.toNat + 8 → ¬ W.Kept a := fun a h1 h2 =>
    (hroom.2.2 a h1 h2).2.2
  have hKout : ∀ a, W.Kept a → a < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ a := fun a ha => by
    by_contra hc; exact hKroom a (by omega) (by omega) ha
  have eA0 : (sp - 8#64 + 0xffffffffffffffa0#64).toNat = sp.toNat - 0x68 :=
    (fp_neg sp 0x60 (by omega) (by decide) (by decide)).trans (by omega)
  have e58 : (sp - 8#64 + 0xffffffffffffff58#64).toNat = sp.toNat - 0xb0 :=
    (fp_neg sp 0xa8 (by omega) (by decide) (by decide)).trans (by omega)
  have eHR : (b + 0xa160#64).toNat = b.toNat + 0xa160 := addr_toNat (by omega)
  have hHRimg : W.Kept (b + 0xa160#64).toNat := Or.inl (by rw [I, eHR]; exact ⟨by omega, by omega⟩)
  have hHRout := hKout _ hHRimg
  -- the call
  refine call2b81 I hb hB.done hMA hrip
    (by rw [e336]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)) ?_
  have csp : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsp).toNat = sp.toNat - 336 := by
    rw [callEntry_rsp]; exact e336
  have hpushK : Keeps (fun a => a < sp.toNat - 336 ∨ sp.toNat - 328 ≤ a) v.m.memory
      (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory := by
    rw [callEntry_mem]; exact pushMem_keeps fun x hx => by rw [e336]; omega
  have hpushKK : Keeps W.Kept v.m.memory (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory :=
    hpushK.mono fun a ha => by rcases hKout a ha with h | h <;> omega
  have hpushI : Keeps (ImgW b) v.m.memory (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory :=
    hpushKK.mono fun a ha => Or.inl (by rw [I]; exact ha.1)
  have hcperm : ∀ acc a, (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory.permits acc a =
      v.m.memory.permits acc a := fun _ _ => by rw [callEntry_mem]; rfl
  have hroomC : Room W (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory sp 4096 :=
    hroom.keeps fun a _ _ acc => hcperm acc a
  have hpr : v.m.memory.Permitted .read (v.m.core.read .rsp - 8#64).toNat 8 := by
    rw [e336]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hpw : v.m.memory.Permitted .write (v.m.core.read .rsp - 8#64).toNat 8 := by
    rw [e336]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hretC : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory.readBytes
      ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x2b86#64]) := by
    rw [callEntry_rsp, callEntry_mem]; exact pushMem_read hpr hpw
  have hMc : ShaMemAll b lb kb sr sc (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory :=
    hB.mem.keepW hb hpushI
  have hMAc : ShaMainAll b (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory := hMA.keepW hb hpushI
  have cfs : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.fsBase = v.m.core.fsBase := rfl
  have crdi : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rdi = b + 0x716e#64 := by
    rw [callEntry_read _ _ _ (by decide)]; exact hrdi
  have crsi : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsi).toNat = sp.toNat - 0x68 := by
    rw [callEntry_read _ _ _ (by decide), hrsi]; exact eA0
  have crdx : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rdx).toNat = sp.toNat - 0xb0 := by
    rw [callEntry_read _ _ _ (by decide), hrdx]; exact e58
  have e716 : (b + 0x716e#64).toNat = b.toNat + 0x716e := addr_toNat (by omega)
  have hlo8 : E.S.lo ≤ (v.m.core.read .rsp - 8#64).toNat := by rw [e336]; omega
  have hrwC : ShaRw b (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory := fun j hj => by
    rw [hcperm, hcperm]; exact hrw j hj
  have hEntry : DigEntryStdin E W b lb kb (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) g Fi (stdinSt data) := by
    refine ⟨rfl, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of (by rw [csp]; omega) hretC,
      ⟨by rw [csp]; omega, by rw [csp]; omega, fun a h1 h2 => by
        rw [csp] at h1 h2; rw [hcperm, hcperm]; exact hroom.2.2 a (by omega) (by omega)⟩,
      by rw [csp]; omega, hB.done, ⟨hMc.cl, hMc.dg⟩, by rw [crdi]; exact hMc.mn.dash,
      fun j hj => by rw [crdi, e716]; exact Or.inl (by rw [I]; exact ⟨by omega, by omega⟩), by rw [crdi, e716]; omega,
      fun a ha => ?_, ?_, ?_, ?_, ?_, by rw [crsi, crdx]; omega, ?_, by rw [cfs]; exact hgk,
      by rw [cfs]; exact hgHR, hMc.mn.stdinV, ?_, hvark, hvarHR, hfi0, ?_, hPA _ _ hHRimg, ?_, ?_,
      by rw [callEntry_mem]; exact file_push hin hlo8, ⟨rfl, rfl, rfl, by show 0 < 2 ^ 31; decide, fun h => by cases h⟩,
      hres⟩
    · simp only [DX, crsi, crdx] at ha
      refine ⟨hKroom a (by omega) (by omega), by rw [csp]; omega⟩
    · rw [crsi]; exact room_perm hroomC (Or.inr rfl) (by omega) (by omega)
    · rw [crsi]; exact room_perm hroomC (Or.inl rfl) (by omega) (by omega)
    · rw [crdx]; exact room_perm hroomC (Or.inr rfl) (by omega) (by omega)
    · rw [crdx]; exact room_perm hroomC (Or.inl rfl) (by omega) (by omega)
    · rw [cfs, loadN_keeps hpushKK (fun j hj => hgk j hj)]; exact hg
    · rw [loadN_keeps hpushKK (fun j hj => hvark j hj)]; exact hvar
    · exact shaRw_perm (o := 0) (n := 1) hb hrwC (Or.inr rfl) (by decide)
    · exact shaRw_perm (o := 0) (n := 1) hb hrwC (Or.inl rfl) (by decide)
    · rw [loadN_keeps hpushKK (fun j hj => Or.inl (by
        rw [I, addr_toNat (by omega)]; exact ⟨by omega, by omega⟩))]; exact hclr
  refine task_digestStdin D Q _ g Fi (stdinSt data) hEntry ?_
  intro t hX
  have hkt := hX.keep
  have hd_t : t.g.done = none := by rw [hX.g]; exact hB.done
  have hvt : Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 0x68 ≤ a ∧ a < sp.toNat - 0x48) ∧
      a ≠ sp.toNat - 0xb0 ∧ a ≠ (b + 0xa160#64).toNat) v.m.memory t.m.memory := by
    refine (hpushK.mono fun a ha => ?_).trans (hkt.mono fun a ha => ⟨?_, ?_⟩)
    · rcases ha.1 with h | h
      · rcases hKout a h with h' | h' <;> omega
      · omega
    · rcases ha.1 with h | h
      · exact Or.inl h
      · right; rw [csp]; omega
    · intro hc
      simp only [DX, crsi, crdx, HR] at hc
      obtain ⟨-, h2, h3, h4⟩ := ha
      rcases hc with (h | h) | h <;> omega
  have hImgT : Keeps (ImgW b) (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory t.m.memory :=
    hkt.mono fun a ha => ⟨Or.inl (Or.inl (by rw [I]; exact ha.1)), fun hc => by
      have hK : W.Kept a := by rw [World.Kept, I]; exact Or.inl ha.1
      have := hKout a hK
      simp only [DX, crsi, crdx, HR, eHR] at hc
      simp only [ImgW, ShaImg] at ha
      rcases hc with (h | h) | h <;> omega⟩
  have hMt : ShaMemAll b lb kb sr sc t.m.memory := hMc.keepW hb hImgT
  have hMAt : ShaMainAll b t.m.memory := hMAc.keepW hb hImgT
  have hsv6 : ∀ p ∈ sv6 sB, 8 ≤ p.1 ∧ p.1 ≤ 48 := by
    intro q hq
    simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨hBt, hript, hrspt, hcst⟩ := body_now (F := fun a => DX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a ∨ HR b a)
    hB (by omega) hsv6 (by omega) (by omega) hX.abi hkt hX.perm
    (fun a hF h1 h2 acc => by
      rcases hF with hF | hF
      · rw [hX.permDX.perm a hF acc, hcperm]
      · simp only [HR] at hF; rw [hspB] at h1 h2; omega)
    (fun a hF => by
      rw [hspB]
      rcases hF with hF | hF
      · simp only [DX, crsi, crdx] at hF; omega
      · simp only [HR] at hF; omega)
    hMt hX.fs hd_t
  have hcs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], r ∈ Silmaril.X86.sysv64.calleeSaved := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Silmaril.X86.sysv64_calleeSaved]
  refine step2b86 I hb hd_t hMAt hript (low8_of_low32 hX.ok) ?_
  intro w hwr hwm hwg hwR hwf
  have wreg : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], w.m.core.read r = v.m.core.read r := fun r hr => by
    rw [hwR, hcst r (hcs r hr)]
  have hwd : w.g.done = none := by rw [hwg]; exact hd_t
  have hfiC : ∀ f st', E.S.file v.m.memory f st' →
      E.S.file (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory f st' := fun f st' h => by
    rw [callEntry_mem]; exact file_push h hlo8
  have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by omega)
  have hPE : PrintEntry E W b lb sc (reb sB t.m.memory) w sp (sha256 data) [0x2d#8] sto := by
    refine ⟨BodyX.withM (hBt.of_eq hwm (hwR .rsp) hwf (by rw [hwd, hd_t])) (by rw [hwm]; exact hMt.pr),
      hspB, hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, by rw [hwm]; exact hMt.mn.delim, ?_, ?_,
      hoe, ?_, hfk, hfw, by omega, hal, hrel⟩
    · rw [wreg .rbp (by simp)]; exact hrbp
    · rw [wreg .rbx (by simp), hrbx, m60_eq]
    · rw [wreg .r14 (by simp)]; exact hr14
    · rw [hwm, ← m60_eq, eA0, ← crsi]; exact hX.digest
    · exact Silmaril.Process.Memory.readWith_length hX.digest
    · exact ⟨by decide, by rw [wreg .r12 (by simp), hr12, hwm]; exact hMt.mn.dash⟩
    · intro j hj; rw [wreg .r12 (by simp), hr12, e716]; simp at hj; exact Or.inl (by rw [I]; exact ⟨by omega, by omega⟩)
    · intro j hj
      refine hPA _ _ ?_
      rw [wreg .r12 (by simp), hr12, e716, World.Kept, I]; simp at hj; exact Or.inl ⟨by omega, by omega⟩
    · rw [hwm, hvt.readBytes (fun j hj => ⟨Or.inr (by omega), by omega, by omega, by omega⟩)]; exact htag
    · rw [hwm, hvt.readBytes (fun j hj => ⟨Or.inr (by omega), by omega, by omega, by omega⟩)]; exact hbin
    · rw [hwm, loadN_keeps hvt (fun j hj => by
        have hK : W.Kept ((b + 0xa178#64).toNat + j) := by
          rw [World.Kept, I, e78]; exact Or.inl ⟨by omega, by omega⟩
        have := hKout _ hK
        refine ⟨Or.inl hK, by omega, by omega, by rw [eHR, e78]; omega⟩)]
      exact hlen
    · rw [hwm]; exact ⟨hX.streams _ _ (Ne.symm hFo) (hfiC _ _ hout.1), hout.2⟩
    · rw [hwm]
      refine hvars.keepR (hvt.mono fun a ha => ?_)
      have hK : W.Kept a := by
        have := hvars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
        rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
          simp only [VarR] at ha; omega] at this
      have := hKout a hK
      refine ⟨Or.inl hK, by omega, by omega, fun he => ?_⟩
      exact hImgVar _ (by rw [he, eHR]; exact ⟨by omega, by omega⟩) ha
  refine task_printLine P hPL hSD Q (reb sB t.m.memory) w sp (sha256 data) [0x2d#8] sto hPE ?_
  intro x hPX
  have hwx : Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 256 ≤ a ∧ a < sp.toNat - 252) ∧
      a ≠ sp.toNat - 244) t.m.memory x.m.memory := by rw [← hwm]; exact hPX.frame
  have hImgX : Keeps (ImgW b) t.m.memory x.m.memory := hwx.mono fun a ha => by
    have hK : W.Kept a := by rw [World.Kept, I]; exact Or.inl ha.1
    have := hKout a hK
    exact ⟨Or.inl hK, by omega, by omega⟩
  have hKx : Keeps W.Kept t.m.memory x.m.memory := hwx.mono fun a hK => by
    have := hKout a hK
    exact ⟨Or.inl hK, by omega, by omega⟩
  refine k x (reb sB t.m.memory) rfl rfl (BodyX.withM hPX.body (hMt.keepW hb hImgX)) (hMAt.keepW hb hImgX)
    hPX.rip (fun r hr => by rw [hPX.cs r hr]; exact wreg r hr) (by rw [hPX.body.fs, hB.fs]; rfl)
    (Keeps.trans (hvt.mono fun a ha => ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1⟩)
      (hwx.mono fun a ha => ⟨ha.1, ha.2.2.2.2⟩)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hKx.readBytes (fun j hj => by simp at hj; subst hj; exact hHRimg)]; exact hX.hr
  · obtain ⟨st', h1, h2, h3, h4, -, h6, h7⟩ := hX.stdin
    exact ⟨st', hPX.streams Fi st' hFo (by rw [hwm]; exact h1), h2, h3, h4, h6, h7⟩
  · obtain ⟨st', hs, he, -, -, hrdg, ho⟩ := hPX.out
    refine ⟨st', hs, he, hrdg, ?_⟩
    rw [ho, hwg, hX.g]
    simp [stdinLine, Proc.Ghost.alloc]
  · rw [hPX.ghost.1, hwg, hX.g]; rfl
  · rw [hPX.ghost.2.1, hwg, hX.g]; rfl
  · exact hPX.ghost.2.2.1
  · intro f st' h1 h2 hf
    exact hPX.streams f st' h2 (by rw [hwm]; exact hX.streams f st' h1 (hfiC _ _ hf))

end Silmaril.Elf.Link.Dyn.Sha256sum
