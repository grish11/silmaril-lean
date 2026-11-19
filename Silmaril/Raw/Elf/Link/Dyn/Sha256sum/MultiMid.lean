module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailMid
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestFile
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiSpec

/-! # GNU `sha256sum FILE…`: one operand, from the call of `digest_file` to the end of its line

`mid_file` (`0x2b81` → `0x2c8a`): `call digest_file` (`call2b81`), `digest_file (name, …)` on a
readable file (`task_digestFile`), `test al` (`0x2b86`), and the result line
(`task_printLine`): `stdout` receives `fileLineM data name`. The file analogue of
`TailMid.tail_mid` (standard input): no `have_read_stdin`, no `stdin` stream; the name is any
C string in the kept memory (an argument) that does not start with `-` and needs no escaping.
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

/-- The first byte of a C string not starting with `-` is not `-`. -/
theorem notDash_of_cstr {m : Memory} {p : Word} {n : List Byte} (h : CStr m p n) (hn : n.head? ≠ some 0x2d#8) :
    ∀ c0, m.readBytes p.toNat 1 = some [c0] → c0 ≠ 0x2d#8 := by
  intro c0 hc0
  have h1 := Memory.readBytes_sub_range h.2 (offset := 0) (len := 1) (by omega) (by omega)
  simp only [Nat.add_zero, List.drop_zero] at h1
  rw [hc0] at h1
  cases n with
  | nil => simp at h1; rw [h1]; decide
  | cons c cs =>
    simp at h1; rw [h1]; intro he; exact hn (by simp [he])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **From the call of `digest_file (name)` to the end of the result line** (`0x2b81` →
`0x2c8a`), on a readable file: `digest_file` returns true and `stdout` receives
`hex(SHA-256(data)) ++ "  " ++ name ++ "\n"`. -/
theorem mid_file {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (D : DigImps E R W b lb kb) (P : PrintImps E W b lb sc) (hPL : PutcLaw E) (hSD : StreamsDisj E)
    (hPA : PrivApart E W) {Q : PState → Prop} {sB v : PState} {sp : Word}
    (hspB : sB.m.core.read .rsp = sp)
    (hB : Body W (ShaMemAll b lb kb sr sc) sB v 328 4096 (sv6 sB)) (hMA : ShaMainAll b v.m.memory)
    (hrip : v.m.core.rip = b + 0x2b81#64) (hrbp : v.m.core.read .rbp = sp - 8#64) {p : Word}
    (hrdi : v.m.core.read .rdi = p) (hr12 : v.m.core.read .r12 = p)
    (hrsi : v.m.core.read .rsi = sp - 8#64 + 0xffffffffffffffa0#64)
    (hrbx : v.m.core.read .rbx = sp - 8#64 + 0xffffffffffffffa0#64)
    (hrdx : v.m.core.read .rdx = sp - 8#64 + 0xffffffffffffff58#64)
    (hr14 : v.m.core.read .r14 = b + 0x7238#64)
    (hlo : E.S.lo + 4096 ≤ sp.toNat) (hal : sp.toNat % 16 = 8)
    {g : Word} (hg : loadN v.m.memory (v.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((v.m.core.fsBase + 0x28#64).toNat + j))
    {name : List Byte} {data : Silmaril.Apps.Sha256sum.Bytes} (hname : CStr v.m.memory p name)
    (hnamek : ∀ j, j < name.length + 1 → W.Kept (p.toNat + j)) (hnd : name.head? ≠ some 0x2d#8)
    (hnoEsc : ∀ c ∈ name, c ≠ 0x5c#8 ∧ c ≠ 0x0a#8 ∧ c ≠ 0x0d#8)
    (hfile : E.fs (toSpec name) = .ok data)
    {sto : St} (hout : StdoutIs E v.m.memory sto) (hoe : sto.err = false)
    (hvars : StdVars E W lb v.m.memory)
    (hfk : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a)
    (hfw : E.stdoutF.toNat + 0x38 < 2 ^ 64) (hrel : W.reliable = true)
    (htag : v.m.memory.readBytes (sp.toNat - 216) 1 = some [0#8])
    (hbin : v.m.memory.readBytes (sp.toNat - 208) 4 = some [0xff#8, 0xff#8, 0xff#8, 0xff#8])
    (hlen : loadN v.m.memory (b + 0xa178#64) 8 = some 0x40#64)
    (hres : InMain v.g ∧ v.g.files < E.maxOpen ∧ data.length ≤ E.maxFile ∧ v.g.allocs < E.maxAllocs ∧
      v.g.heap + 0x8048 ≤ E.maxHeap)
    (k : ∀ x sR : PState, sR.m.core = sB.m.core → sR.g = sB.g →
      Body W (ShaMemAll b lb kb sr sc) sR x 328 4096 (sv6 sR) → ShaMainAll b x.m.memory →
      x.m.core.rip = b + 0x2c8a#64 →
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], x.m.core.read r = v.m.core.read r) →
      x.m.core.fsBase = v.m.core.fsBase →
      Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 0x68 ≤ a ∧ a < sp.toNat - 0x48) ∧
        a ≠ sp.toNat - 0xb0 ∧ ¬ (sp.toNat - 256 ≤ a ∧ a < sp.toNat - 252) ∧
        a ≠ sp.toNat - 244) v.m.memory x.m.memory →
      (∃ st', StdoutIs E x.m.memory st' ∧ st'.err = false ∧ st'.reading = sto.reading ∧
        x.g.out ++ st'.buf = v.g.out ++ sto.buf ++ fileLineM data name) →
      x.g.jobs = v.g.jobs → x.g.atexit = v.g.atexit → x.g.done = none → x.g.err = v.g.err →
      (x.g.allocs = v.g.allocs + 1 ∧ x.g.heap = v.g.heap + 0x8048 ∧ x.g.files = v.g.files + 1) →
      (∀ f st', f ≠ E.stdoutF → E.S.file v.m.memory f st' → E.S.file x.m.memory f st') →
      LibK E W v.m.memory x.m.memory → MustQ W Q x) : MustQ W Q v := by
  have I := D.cl.img
  have hb := D.cl.hb
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
  have crdi : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rdi = p := by
    rw [callEntry_read _ _ _ (by decide)]; exact hrdi
  have crsi : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsi).toNat = sp.toNat - 0x68 := by
    rw [callEntry_read _ _ _ (by decide), hrsi]; exact eA0
  have crdx : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rdx).toNat = sp.toNat - 0xb0 := by
    rw [callEntry_read _ _ _ (by decide), hrdx]; exact e58
  have hnameC : CStr (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory p name :=
    cstr_keeps hpushKK hname hnamek
  have hEntry : DigEntry E W b lb kb (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) name data g := by
    refine ⟨rfl, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of (by rw [csp]; omega) hretC,
      ⟨by rw [csp]; omega, by rw [csp]; omega, fun a h1 h2 => by
        rw [csp] at h1 h2; rw [hcperm, hcperm]; exact hroom.2.2 a (by omega) (by omega)⟩,
      by rw [csp]; omega, hB.done, ⟨hMc.cl, hMc.dg⟩, by rw [crdi]; exact hnameC,
      by rw [crdi]; exact hnamek, by rw [crdi]; exact notDash_of_cstr hnameC hnd, hfile,
      fun a ha => ?_, ?_, ?_, ?_, ?_, by rw [crsi, crdx]; omega, ?_, by rw [cfs]; exact hgk, hres⟩
    · simp only [DX, crsi, crdx] at ha
      refine ⟨hKroom a (by omega) (by omega), by rw [csp]; omega⟩
    · rw [crsi]; exact room_perm hroomC (Or.inr rfl) (by omega) (by omega)
    · rw [crsi]; exact room_perm hroomC (Or.inl rfl) (by omega) (by omega)
    · rw [crdx]; exact room_perm hroomC (Or.inr rfl) (by omega) (by omega)
    · rw [crdx]; exact room_perm hroomC (Or.inl rfl) (by omega) (by omega)
    · rw [cfs, loadN_keeps hpushKK (fun j hj => hgk j hj)]; exact hg
  have hLc : LibK E W v.m.memory (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory := by
    rw [callEntry_mem]; exact (LibK.refl E W _).push (by rw [e336]; omega)
  refine task_digestFile D Q _ name data g hEntry ?_
  intro t hX
  have hkt := hX.keep
  have hd_t : t.g.done = none := by rw [hX.g]; exact hB.done
  have hvt : Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 0x68 ≤ a ∧ a < sp.toNat - 0x48) ∧
      a ≠ sp.toNat - 0xb0) v.m.memory t.m.memory := by
    refine (hpushK.mono fun a ha => ?_).trans (hkt.mono fun a ha => ⟨?_, ?_⟩)
    · rcases ha.1 with h | h
      · rcases hKout a h with h' | h' <;> omega
      · omega
    · rcases ha.1 with h | h
      · exact Or.inl h
      · right; rw [csp]; omega
    · intro hc
      simp only [DX, crsi, crdx] at hc
      obtain ⟨-, h2, h3⟩ := ha
      rcases hc with h | h <;> omega
  have hImgT : Keeps (ImgW b) (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory t.m.memory :=
    hkt.mono fun a ha => ⟨Or.inl (Or.inl (by rw [I]; exact ha.1)), fun hc => by
      have hK : W.Kept a := by rw [World.Kept, I]; exact Or.inl ha.1
      have := hKout a hK
      simp only [DX, crsi, crdx] at hc
      rcases hc with h | h <;> omega⟩
  have hMt : ShaMemAll b lb kb sr sc t.m.memory := hMc.keepW hb hImgT
  have hMAt : ShaMainAll b t.m.memory := hMAc.keepW hb hImgT
  have hsv6 : ∀ p ∈ sv6 sB, 8 ≤ p.1 ∧ p.1 ≤ 48 := by
    intro q hq
    simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨hBt, hript, hrspt, hcst⟩ := body_now (F := fun a => DX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a)
    hB (by omega) hsv6 (by omega) (by omega) hX.abi hkt hX.perm
    (fun a hF h1 h2 acc => by rw [hX.permDX.perm a hF acc, hcperm])
    (fun a hF => by
      rw [hspB]
      simp only [DX, crsi, crdx] at hF; omega)
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
    rw [callEntry_mem]; exact file_push h (by rw [e336]; omega)
  have e78 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (by omega)
  have hnamet : CStr t.m.memory p name := cstr_keeps hvt hname fun j hj => by
    have := hKout _ (hnamek j hj)
    exact ⟨Or.inl (hnamek j hj), by omega, by omega⟩
  have hPE : PrintEntry E W b lb sc (reb sB t.m.memory) w sp (sha256 (ofSpec data)) name sto := by
    refine ⟨BodyX.withM (hBt.of_eq hwm (hwR .rsp) hwf (by rw [hwd, hd_t])) (by rw [hwm]; exact hMt.pr),
      hspB, hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnoEsc, ?_, ?_, by rw [hwm]; exact hMt.mn.delim, ?_, ?_,
      hoe, ?_, hfk, hfw, by omega, hal, hrel⟩
    · rw [wreg .rbp (by simp)]; exact hrbp
    · rw [wreg .rbx (by simp), hrbx, m60_eq]
    · rw [wreg .r14 (by simp)]; exact hr14
    · rw [hwm, ← m60_eq, eA0, ← crsi]; exact hX.digest
    · exact Silmaril.Process.Memory.readWith_length hX.digest
    · rw [wreg .r12 (by simp), hr12, hwm]; exact hnamet
    · intro j hj; rw [wreg .r12 (by simp), hr12]; exact hnamek j hj
    · intro j hj
      refine hPA _ _ ?_
      rw [wreg .r12 (by simp), hr12]; exact hnamek j hj
    · rw [hwm, hvt.readBytes (fun j hj => ⟨Or.inr (by omega), by omega, by omega⟩)]; exact htag
    · rw [hwm, hvt.readBytes (fun j hj => ⟨Or.inr (by omega), by omega, by omega⟩)]; exact hbin
    · rw [hwm, loadN_keeps hvt (fun j hj => by
        have hK : W.Kept ((b + 0xa178#64).toNat + j) := by
          rw [World.Kept, I, e78]; exact Or.inl ⟨by omega, by omega⟩
        have := hKout _ hK
        refine ⟨Or.inl hK, by omega, by omega⟩)]
      exact hlen
    · rw [hwm]; exact ⟨hX.streams _ _ (hfiC _ _ hout.1), hout.2⟩
    · rw [hwm]
      refine hvars.keepR (hvt.mono fun a ha => ?_)
      have hK : W.Kept a := by
        have := hvars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
        rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
          simp only [VarR] at ha; omega] at this
      have := hKout a hK
      exact ⟨Or.inl hK, by omega, by omega⟩
  refine task_printLine P hPL hSD Q (reb sB t.m.memory) w sp (sha256 (ofSpec data)) name sto hPE ?_
  intro x hPX
  have hwx : Keeps (fun a => (W.Kept a ∨ sp.toNat - 328 ≤ a) ∧ ¬ (sp.toNat - 256 ≤ a ∧ a < sp.toNat - 252) ∧
      a ≠ sp.toNat - 244) t.m.memory x.m.memory := by rw [← hwm]; exact hPX.frame
  have hImgX : Keeps (ImgW b) t.m.memory x.m.memory := hwx.mono fun a ha => by
    have hK : W.Kept a := by rw [World.Kept, I]; exact Or.inl ha.1
    have := hKout a hK
    exact ⟨Or.inl hK, by omega, by omega⟩
  refine k x (reb sB t.m.memory) rfl rfl (BodyX.withM hPX.body (hMt.keepW hb hImgX)) (hMAt.keepW hb hImgX)
    hPX.rip (fun r hr => by rw [hPX.cs r hr]; exact wreg r hr) (by rw [hPX.body.fs, hB.fs]; rfl)
    (Keeps.trans (hvt.mono fun a ha => ⟨ha.1, ha.2.1, ha.2.2.1⟩)
      (hwx.mono fun a ha => ⟨ha.1, ha.2.2.2⟩)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (((hLc.trans hX.lib).of_eq hwm).trans hPX.lib)
  · obtain ⟨st', hs, he, -, -, hrdg, ho⟩ := hPX.out
    refine ⟨st', hs, he, hrdg, ?_⟩
    rw [ho, hwg, hX.g]
    simp [fileLineM, Proc.Ghost.alloc, Proc.Ghost.opened]
  · rw [hPX.ghost.1, hwg, hX.g]; rfl
  · rw [hPX.ghost.2.1, hwg, hX.g]; rfl
  · exact hPX.ghost.2.2.1
  · rw [hPX.gerr, hwg, hX.g]; simp [Proc.Ghost.alloc, Proc.Ghost.opened, callEntry_g]
  · obtain ⟨-, -, -, -, hal, hhp, hfi⟩ := hPX.ghost
    rw [hal, hhp, hfi, hwg, hX.g]
    simp [Proc.Ghost.alloc, Proc.Ghost.opened, callEntry_g]
  · intro f st' h1 hf
    exact hPX.streams f st' h1 (by rw [hwm]; exact hX.streams f st' (hfiC _ _ hf))

end Silmaril.Elf.Link.Dyn.Sha256sum
