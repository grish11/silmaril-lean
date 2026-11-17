module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailPre

/-! # GNU `sha256sum`, stdin tier: `main` from the call of `digest_file` to its return

`tail_post`: from `MidAt` (`0x2b81`), `tail_mid` (`digest_file ("-")` and the result line) then
`tail_end` (the loop's end, `rpl_fclose (stdin)`, the guard, the epilogue) reach `main`'s
return to the library (`MainRet`) with `stdinLine data` written. `TailImps`: what the world
must provide for it (the imports with their contracts and the stream laws).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Cert

/-- What `main`'s tail needs of the world: the imports of `digest_file ("-")` (with `lseek`
and the close path) and of the result line, the stream laws the output path uses (`PutcLaw`,
`StreamsDisj`, `PrivApart`, `stdout`'s footprint outside the kept memory and not wrapping),
reliable output, `optind`'s address, and distinct `stdout`/`stderr`. -/
structure TailImps (E : Env) (R : ShaRep) (W : World) (b lb kb sc : Word) : Prop where
  dig : StdinImps E R W b lb kb
  pr : PrintImps E W b lb sc
  putc : PutcLaw E
  disj : StreamsDisj E
  apart : PrivApart E W
  footK : ∀ m st a, E.S.file m E.stdoutF st → E.S.foot m E.stdoutF a → ¬ W.Kept a
  fw : E.stdoutF.toNat + 0x38 < 2 ^ 64
  rel : W.reliable = true
  optA : E.optindA = lb + 0x204248#64
  ne : E.stdoutF ≠ E.stderrF

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`main` from `call digest_file` (`0x2b81`) to its return**, stdin tier. -/
theorem tail_post {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (T : TailImps E R W b lb kb sc)
    {C : Nat → Prop} {fi : Word} {data : List Byte} {Q : PState → Prop} {s v : PState} {g : Word}
    (ht : TailEntry E W b lb s fi g)
    (h : MidAt E W b lb kb sr sc C fi (outSt 1) (outSt 2) (stdinSt data) s v g
      { s.g with atexit := [b + 0x69b0#64] })
    (hout : s.g.out = []) (hjobs : s.g.jobs = [.exitRax])
    (hres : s.g.allocs < E.maxAllocs ∧ s.g.heap + 0x8048 ≤ E.maxHeap)
    (k : ∀ t, MainRet E W b lb s t (stdinLine data) → MustQ W Q t) : MustQ W Q v := by
  have I := T.dig.dig.cl.img
  have hb := T.dig.dig.cl.hb
  have hroom : Room W v.m.memory (s.m.core.read .rsp) 4096 := h.body.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := ht.lo
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => by by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [I]; exact ha)
  have eHR : (b + 0xa160#64).toNat = b.toNat + 0xa160 := addr_toNat (by omega)
  have hHR : ∀ a, ¬ ShaImg b a → a ≠ (b + 0xa160#64).toNat := fun a ha he =>
    ha (by rw [he, eHR]; exact ⟨by omega, by omega⟩)
  refine tail_mid T.dig T.pr T.putc T.disj T.apart (sB := reb s v.m.memory) (sp := s.m.core.read .rsp) rfl
    h.body h.ma h.rw h.rip h.rbp h.rdi h.r12 h.rsi h.rbx h.rdx h.r14 ht.lo ht.al h.clr (g := g)
    (by rw [h.fs]; exact h.guard) (by rw [h.fs]; exact ht.guardk)
    (by rw [h.fs]; exact fun j hj => hHR _ (ht.guardImg j hj)) h.var ht.vark
    (fun j hj => hHR _ (ht.varImg j hj)) ht.fi0 h.env.inp ht.fiO ⟨h.env.out, rfl⟩ rfl h.env.vars ht.imgVar
    T.footK T.fw T.rel h.tag h.bin h.len (by rw [h.ghost]; exact ⟨⟨[], hjobs⟩, hres.1, hres.2⟩) ?_
  intro x sR hcR hgR hBx hMAx hripx hregs hfsx hKx hhr hstdin hstdout hjx hax hdx hstreams
  have hsx : ∀ a, (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) →
      ¬ ((s.m.core.read .rsp).toNat - 0x68 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 0x48) →
      a ≠ (s.m.core.read .rsp).toNat - 0xb0 → a ≠ (b + 0xa160#64).toNat →
      ¬ ((s.m.core.read .rsp).toNat - 256 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 252) →
      a ≠ (s.m.core.read .rsp).toNat - 244 →
      (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) ∧
      ¬ ((s.m.core.read .rsp).toNat - 0x68 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 0x48) ∧
      a ≠ (s.m.core.read .rsp).toNat - 0xb0 ∧ a ≠ (b + 0xa160#64).toNat ∧
      ¬ ((s.m.core.read .rsp).toNat - 256 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 252) ∧
      a ≠ (s.m.core.read .rsp).toNat - 244 := fun a h1 h2 h3 h4 h5 h6 => ⟨h1, h2, h3, h4, h5, h6⟩
  -- a kept address outside the image survives `0x2b81` → `0x2c8a`
  have hKO : ∀ a, W.Kept a → ¬ ShaImg b a → _ := fun a hK hI =>
    have := hKout a hK
    hsx a (Or.inl hK) (by omega) (by omega) (hHR a hI) (by omega) (by omega)
  have hKI : ∀ a, ShaImg b a → a ≠ (b + 0xa160#64).toNat → _ := fun a hI hne =>
    have := hKout a (hImgK a hI)
    hsx a (Or.inl (hImgK a hI)) (by omega) (by omega) hne (by omega) (by omega)
  have hS : ∀ a, (s.m.core.read .rsp).toNat - 328 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      ¬ ((s.m.core.read .rsp).toNat - 0x68 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 0x48) →
      a ≠ (s.m.core.read .rsp).toNat - 0xb0 →
      ¬ ((s.m.core.read .rsp).toNat - 256 ≤ a ∧ a < (s.m.core.read .rsp).toNat - 252) →
      a ≠ (s.m.core.read .rsp).toNat - 244 → _ := fun a h1 h2 h3 h4 h5 h6 =>
    hsx a (Or.inr h1) h3 h4 (hHR a fun hI => (hroom.2.2 a (by omega) (by omega)).2.2 (hImgK a hI)) h5 h6
  have e18 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64).toNat = (s.m.core.read .rsp).toNat - 240 :=
    (fp_neg _ 0xe8 (by omega) (by decide) (by decide)).trans (by omega)
  have e28 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64).toNat = (s.m.core.read .rsp).toNat - 224 :=
    (fp_neg _ 0xd8 (by omega) (by decide) (by decide)).trans (by omega)
  obtain ⟨st', hf1, -, -, hf4, hf5, hf6⟩ := hstdin
  have hvx : x.m.core.read .rbp = v.m.core.read .rbp := hregs .rbp (by simp)
  have hvx15 : x.m.core.read .r15 = v.m.core.read .r15 := hregs .r15 (by simp)
  have hend : loadN x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64) 8 =
      some (s.m.core.read .rsi + 16#64) := by
    rw [loadN_keeps (a := s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64) (n := 8) hKx (fun j hj => by
      rw [e18]
      exact hS ((s.m.core.read .rsp).toNat - 240 + j) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))]
    exact h.endp
  have hok : loadN x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 = some 1#64 := by
    rw [loadN_keeps (a := s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) (n := 1) hKx (fun j hj => by
      rw [e28]
      exact hS ((s.m.core.read .rsp).toNat - 224 + j) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))]
    exact h.ok
  have hvarx : loadN x.m.memory (lb + 0x2056b0#64) 8 = some fi := by
    rw [loadN_keeps (a := lb + 0x2056b0#64) (n := 8) hKx (fun j hj => hKO _ (ht.vark j hj) (ht.varImg j hj))]
    exact h.var
  have hgsx : x.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [g]) := by
    rw [hKx.readBytes (fun j hj => hS ((s.m.core.read .rsp).toNat - 64 + j) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))]
    exact h.guards
  have hgx : loadN x.m.memory (x.m.core.fsBase + 0x28#64) 8 = some g := by
    rw [hfsx, h.fs, loadN_keeps (a := s.m.core.fsBase + 0x28#64) (n := 8) hKx
      (fun j hj => hKO _ (ht.guardk j hj) (ht.guardImg j hj))]
    exact h.guard
  have hretx : x.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [W.gate]) := by
    rw [hKx.readBytes (fun j hj => hS ((s.m.core.read .rsp).toNat + j) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))]
    exact h.ret
  refine tail_end T.dig.dig.cl T.dig.dig.lseek (sB := sR) (sp := s.m.core.read .rsp) (av := s.m.core.read .rsi)
    (g := g) (Fi := fi) (R := W.gate) (by rw [hcR]; rfl) hBx hMAx hripx (by rw [hvx]; exact h.rbp) ht.lo ht.al
    (by rw [hvx15]; exact h.r15) ht.av hend hok (by rw [loadN_rb rfl hhr]; rfl) hvarx ht.vark
    hf1 hf5 hf4 (by rw [hf6]; decide) (by rw [hf6]; decide) hgsx hgx (by rw [hfsx, h.fs]; exact ht.guardk)
    hretx ?_
  intro t hrt hrax hgo hgj hga hgd hKt hst hft
  have hvg := h.ghost
  have hKv : Keeps (fun a => W.Kept a ∧ ¬ ShaImg b a) v.m.memory t.m.memory :=
    (hKx.mono fun a ha => hKO a ha.1 ha.2).trans (hKt.mono fun a ha => ha.1)
  have hImgW : ∀ n, n < 0xa160 → ImgW b (b + BitVec.ofNat 64 n).toNat ∧ (b + BitVec.ofNat 64 n).toNat ≠
      (b + 0xa160#64).toNat := fun n hn => by
    rw [addr_toNat (by omega), eHR]; exact ⟨⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩, by omega⟩
  have hKi : Keeps (fun a => ImgW b a ∧ a ≠ (b + 0xa160#64).toNat) v.m.memory t.m.memory :=
    (hKx.mono fun a ha => hKI a ha.1.1 ha.2).trans (hKt.mono fun a ha => hImgK a ha.1.1)
  have e40 : ∀ j, j < 1 → (b + 0xa040#64).toNat + j = (b + BitVec.ofNat 64 (0xa040 + j)).toNat := fun j hj => by
    rw [addr_toNat (by omega), addr_toNat (by omega)]; omega
  obtain ⟨so, hso, hse, hsr, hsb⟩ := hstdout
  refine k t ⟨hrt, hrax, ⟨by rw [hgj, hjx, hvg]; exact hjobs, by rw [hga, hax, hvg], hgd⟩,
    ⟨so, ⟨hst _ _ (Ne.symm ht.fiO) hso.1, hso.2⟩, hse, hsr, ?_⟩,
    hst _ _ (Ne.symm ht.fiE) (hstreams _ _ (Ne.symm ht.fiE) (Ne.symm T.ne) h.env.err), ?_,
    ⟨hBx.mem.st.keepW hb (hKt.mono fun a ha => hImgK a ha.1), hBx.mem.cl.keepW hb (hKt.mono fun a ha => hImgK a ha.1)⟩,
    by rw [hft, hfsx, h.fs], ?_, ?_⟩
  · rw [hgo, hsb, hvg]; simp [hout, outSt]
  · refine h.env.vars.keepR (hKv.mono fun a ha => ?_)
    have := h.env.vars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
    rw [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
      simp only [VarR] at ha; omega] at this
    exact ⟨this, fun hI => ht.imgVar a hI ha⟩
  · rw [loadN_keeps hKi (fun j hj => by rw [e40 j hj]; exact hImgW _ (by omega))]; exact h.bss
  · exact (hKi.permitted (fun j hj => by rw [e40 j hj]; exact hImgW _ (by omega))).2 h.bssw

end Silmaril.Elf.Link.Dyn.Sha256sum
