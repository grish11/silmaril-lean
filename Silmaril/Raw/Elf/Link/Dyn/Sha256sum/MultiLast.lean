module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiNext

/-! # GNU `sha256sum FILE…`: the end of the operand loop, and the whole loop

* `loop_last` (`0x2c8a` → `main`'s return): after the last operand's line, `eax = ok`
  (`0x2c8a`), the end of the operands (`0x2b57` → `0x2cf9`), `edx = ok` (`0x2cf9`),
  `have_read_stdin` clear (`0x2cfb` → `0x2d08`: no `rpl_fclose (stdin)` on this tier), the
  guard (`0x2d08`), the epilogue and `ret` (`0x2d21`): `main` returns 0 (`MainRet`).
* `multi_loop`: from the call of `digest_file` on the first of the operands `(p, n) :: rest`,
  every run returns from `main` with status 0, `stdout` having received the lines of all of
  them in order (`linesM`), by induction on `rest` (`loop_mid`, then `loop_next` or
  `loop_last`).
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

theorem ult_last {q : Word} (h : q.toNat + 8 * (0 + 1) < 2 ^ 64) :
    (q + 8#64).ult (q + BitVec.ofNat 64 (8 * (0 + 1))) = false := by
  simp only [BitVec.ult, addr_toNat (v := 8) (b := q) (by omega), decide_eq_false_iff_not]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The status `main` returns for the `ok` byte `okv`: `!ok`. -/
def okCode (okv : Word) : BitVec 32 := if okv.setWidth 8 = 1#8 then 0#32 else 1#32

/-- **From the loop's head after the last operand: `main` returns `!ok`** (`0x2b57` → `ret`, K8):
`v1` differs from a state `x` of the invariant (any `ip`, any stored `ok`) only in `rip` and
`eax`, whose low byte is the final `ok` byte `okn` (0 or 1). -/
theorem loop_end {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {Q : PState → Prop} {x v1 : PState} {ip q p g okv okn : Word} {n : List Byte} {X : List Byte}
    (F : LoopFrO E W b lb kb sr sc s x ip q p n [] X g okv) (hokn : okn = 0#64 ∨ okn = 1#64)
    (r1 : v1.m.core.rip = b + 0x2b57#64) (m1 : v1.m.memory = x.m.memory) (g1 : v1.g = x.g)
    (R1 : ∀ r, r ≠ .rax → v1.m.core.read r = x.m.core.read r)
    (al1 : (v1.m.core.read .rax).setWidth 8 = okn.setWidth 8) (f1 : v1.m.core.fsBase = x.m.core.fsBase)
    (k : ∀ t, MainRetG E W b lb s t X (okCode okn) x.g.err → MustQ W Q t) : MustQ W Q v1 := by
  have I := M.dig.cl.img
  have hb := M.dig.cl.hb
  have hB := F.body
  have hroom : Room W x.m.memory (s.m.core.read .rsp) 4096 := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := c.lo
  have hd := hB.done
  have hql := F.qlim
  simp only [List.length_nil] at hql
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hd1 : v1.g.done = none := by rw [g1]; exact hd
  have bp1 : v1.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [R1 _ (by decide)]; exact F.rbp
  have q1 : v1.m.core.read .r15 = q := by rw [R1 _ (by decide)]; exact F.r15
  refine step2b57e I hb hd1 (m1 ▸ F.ma) r1 (endp := q + BitVec.ofNat 64 (8 * (0 + 1)))
    (by rw [m1, bp1]; exact F.endp) (by rw [q1]; exact ult_last hql) ?_
  intro v2 r2 m2 g2 R2 q2 f2
  have hm2 : v2.m.memory = x.m.memory := m2.trans m1
  have hd2 : v2.g.done = none := by rw [g2]; exact hd1
  refine step2cf9 I hb hd2 (hm2 ▸ F.ma) r2 ?_
  intro v3 r3 m3 g3 R3 d3 f3
  have hm3 : v3.m.memory = x.m.memory := m3.trans hm2
  have hd3 : v3.g.done = none := by rw [g3]; exact hd2
  refine step2cfb_f I hb hd3 (hm3 ▸ F.ma) r3 (h := 0#64)
    (by rw [r3, hm3, show b + 0x2cfb#64 + 0x7465#64 = b + 0xa160#64 by rw [BitVec.add_assoc]; rfl]; exact F.hr)
    (by decide) ?_
  intro v4 r4 m4 g4 R4 f4
  have hm4 : v4.m.memory = x.m.memory := m4.trans hm3
  have hd4 : v4.g.done = none := by rw [g4]; exact hd3
  have bp4 : v4.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by
    rw [R4, R3 _ (by decide), R2 _ (by decide) (by decide), bp1]
  have dl4 : (v4.m.core.read .rdx).setWidth 8 = okn.setWidth 8 := by
    rw [R4, d3, sw_a, R2 _ (by decide) (by decide), al1]
  have fs4 : v4.m.core.fsBase = x.m.core.fsBase := by rw [f4, f3, f2, f1]
  have hd01 : okn.setWidth 8 = 0#8 ∨ okn.setWidth 8 = 1#8 := by rcases hokn with rfl | rfl <;> decide
  refine step2d08o I hb hd4 (hm4 ▸ F.ma) r4 dl4 hd01 (g := g) ?_ ?_ ?_
  · rw [hm4, bp4]
    have e : (s.m.core.read .rsp - 8#64 + 0xffffffffffffffc8#64).toNat = (s.m.core.read .rsp).toNat - 64 :=
      (fp_neg _ 0x38 (by omega) (by decide) (by decide)).trans (by omega)
    exact loadN_enc (by rw [e]; exact F.guards)
  · rw [hm4, fs4, F.fs]; exact F.guard
  intro v7 r7 m7 g7 R7 a7 f7
  have hd7 : v7.g.done = none := by rw [g7]; exact hd4
  have rbp7 : v7.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [R7 _ (by decide) (by decide)]; exact bp4
  have hm7 : v7.m.memory = x.m.memory := m7.trans hm4
  have hsv := hB.saved
  simp only [sv6, reb_core, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsv
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsv
  have ad : ∀ k, 8 + k ≤ (s.m.core.read .rsp).toNat → 0 < k → k < 2 ^ 64 →
      (s.m.core.read .rsp - 8#64 + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = (s.m.core.read .rsp).toNat - 8 - k :=
    fun k h1 h2 h3 => fp_neg _ k h1 h2 h3
  refine step2d21 I hb hd7 (hm7 ▸ F.ma) r7 (w1 := s.m.core.read .rbx) (w2 := s.m.core.read .r12)
    (w3 := s.m.core.read .r13) (w4 := s.m.core.read .r14) (w5 := s.m.core.read .r15) (w6 := s.m.core.read .rbp)
    (w7 := W.gate) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hm7, rbp7, show (s.m.core.read .rsp - 8#64 + 0xffffffffffffffd8#64).toNat = (s.m.core.read .rsp).toNat - 48 from
      (ad 0x28 (by omega) (by decide) (by decide)).trans (by omega)]; exact word_rb s6
  · rw [hm7, rbp7, show (s.m.core.read .rsp - 8#64 + 0xffffffffffffffe0#64).toNat = (s.m.core.read .rsp).toNat - 40 from
      (ad 0x20 (by omega) (by decide) (by decide)).trans (by omega)]; exact word_rb s5
  · rw [hm7, rbp7, show (s.m.core.read .rsp - 8#64 + 0xffffffffffffffe8#64).toNat = (s.m.core.read .rsp).toNat - 32 from
      (ad 0x18 (by omega) (by decide) (by decide)).trans (by omega)]; exact word_rb s4
  · rw [hm7, rbp7, show (s.m.core.read .rsp - 8#64 + 0xfffffffffffffff0#64).toNat = (s.m.core.read .rsp).toNat - 24 from
      (ad 0x10 (by omega) (by decide) (by decide)).trans (by omega)]; exact word_rb s3
  · rw [hm7, rbp7, show (s.m.core.read .rsp - 8#64 + 0xfffffffffffffff8#64).toNat = (s.m.core.read .rsp).toNat - 16 from
      (ad 0x8 (by omega) (by decide) (by decide)).trans (by omega)]; exact word_rb s2
  · rw [hm7, rbp7, BitVec.add_zero, e8]; exact word_rb s1
  · rw [hm7, rbp7, BitVec.sub_add_cancel]; exact word_rb F.ret
  intro w8 r8 m8 g8 _ R8 f8
  have hm8 : w8.m.memory = x.m.memory := m8.trans hm7
  have hg8 : w8.g = x.g := by rw [g8, g7, g4, g3, g2, g1]
  obtain ⟨sto, hso, hse, hsr, hsX⟩ := F.out
  refine k w8 ⟨r8, ?_, ⟨by rw [hg8]; exact F.jobs, by rw [hg8]; exact F.atexit, by rw [hg8]; exact hd⟩,
    ⟨sto, by rw [hm8]; exact hso, hse, hsr, by rw [hg8]; exact hsX⟩, by rw [hm8]; exact F.err,
    by rw [hm8]; exact F.vars, by rw [hm8]; exact ⟨hB.mem.st, hB.mem.cl⟩,
    by rw [f8, f7, fs4, F.fs], ⟨by rw [hm8]; exact F.bss, by rw [hm8]; exact F.bssw⟩, by rw [hg8]⟩
  rw [R8 .rax (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a7

/-- **After the last operand: `main` returns `!ok`** (`0x2c8a` → `ret`), any `ok` byte 0 or 1 (K8). -/
theorem loop_lastO {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {Q : PState → Prop} {x : PState} {q p g okv : Word} {n : List Byte} {X : List Byte}
    (F : LoopFrO E W b lb kb sr sc s x (b + 0x2c8a#64) q p n [] X g okv) (hok : okv = 0#64 ∨ okv = 1#64)
    (k : ∀ t, MainRetG E W b lb s t X (okCode okv) x.g.err → MustQ W Q t) : MustQ W Q x :=
  step2c8a M.dig.cl.img M.dig.cl.hb F.body.done F.ma F.rip (ok := okv) (by rw [F.rbp]; exact F.ok)
    fun _ r1 m1 g1 R1 al1 f1 => loop_end M c F hok r1 m1 g1 R1 al1 f1 k

/-- `MainRetG` with status 0 is `MainRet`. -/
theorem MainRetG.toRet {E : Env} {W : World} {b lb : Word} {s t : PState} {X Y : List Byte}
    (h : MainRetG E W b lb s t X 0#32 Y) : MainRet E W b lb s t X :=
  ⟨h.rip, h.rax, h.ghost, h.out, h.err, h.vars, h.mem, h.fs, h.bss⟩

/-- **After the last operand: `main` returns 0** (`0x2c8a` → `ret`). -/
theorem loop_last {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {Q : PState → Prop} {x : PState} {q p g : Word} {n : List Byte} {X : List Byte}
    (F : LoopFr E W b lb kb sr sc s x (b + 0x2c8a#64) q p n [] X g)
    (k : ∀ t, MainRet E W b lb s t X → MustQ W Q t) : MustQ W Q x :=
  loop_lastO M c F (Or.inr rfl) fun t ht => k t (MainRetG.toRet ht)

/-- **The operand loop**, from the call of `digest_file` on the first of `(p, n) :: rest`. -/
theorem multi_loop {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes} {Q : PState → Prop} {g : Word} :
    ∀ (rest : List (Word × List Byte)) (q p : Word) (n : List Byte) (X : List Byte) (v : PState),
      LoopAt E W b lb kb sr sc s v q p n rest X g → (∀ pn ∈ (p, n) :: rest, OpOk E dat pn.2) →
      (∀ t, MainRet E W b lb s t (X ++ linesM dat ((p, n) :: rest)) → MustQ W Q t) → MustQ W Q v := by
  intro rest
  induction rest with
  | nil =>
    intro q p n X v h hop k
    refine loop_mid M c h (hop (p, n) (by simp)) fun x hx _ _ _ _ => loop_last M c hx fun t ht => k t ?_
    simpa [linesM] using ht
  | cons pn rest ih =>
    obtain ⟨p', n'⟩ := pn
    intro q p n X v h hop k
    refine loop_mid M c h (hop (p, n) (by simp)) fun x hx _ _ _ _ => loop_next M c hx fun v' hv' =>
      ih _ _ _ _ v' hv' (fun pn hpn => hop pn (by simp at hpn ⊢; tauto)) fun t ht => k t ?_
    simpa [linesM, List.append_assoc] using ht

end Silmaril.Elf.Link.Dyn.Sha256sum
