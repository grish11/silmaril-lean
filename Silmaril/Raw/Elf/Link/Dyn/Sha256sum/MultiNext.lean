module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiLoop
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiBlocks

/-! # GNU `sha256sum FILE…`: from the end of a line to the next operand's `digest_file`

`loop_next` (`0x2c8a` → `0x2b81`): `eax = ok` (`0x2c8a`), the loop's head with an operand left
(`0x2b57`, `r15 += 8`), `ok` stored back and `r12 = argv[i+1]` (`0x2b6b`), the arguments of
`digest_file` (`0x2b74`). The invariant moves to the next operand; the body is re-based on the
memory after the store at `rbp-0xd8` (`Body.freshK`).
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

theorem endp_succ {q : Word} {k : Nat} (h : q.toNat + 8 * (k + 2) < 2 ^ 64) :
    q + 8#64 + BitVec.ofNat 64 (8 * (k + 1)) = q + BitVec.ofNat 64 (8 * (k + 1 + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [addr_toNat (by rw [addr_toNat (v := 8) (by omega)]; omega), addr_toNat (v := 8) (by omega),
    addr_toNat (by omega)]
  omega

theorem ult_more {q : Word} {k : Nat} (h : q.toNat + 8 * (k + 2) < 2 ^ 64) :
    (q + 8#64).ult (q + BitVec.ofNat 64 (8 * (k + 1 + 1))) = true := by
  simp only [BitVec.ult, addr_toNat (v := 8) (b := q) (by omega), addr_toNat (b := q) (v := 8 * (k + 1 + 1)) (by omega),
    decide_eq_true_eq]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **From the loop's head to the next operand** (`0x2b57` → `0x2b81`, K8): a state `v1` at the
head that differs from a state `x` of the invariant (at any `ip`, with any `ok`) only in `rip` and
`eax`, whose low byte `okn` (0 or 1) is the `ok` byte stored next. -/
theorem loop_head {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {Q : PState → Prop} {x v1 : PState} {ip q p p' g okv okn : Word} {n n' : List Byte}
    {rest : List (Word × List Byte)}
    {X : List Byte} (F : LoopFrO E W b lb kb sr sc s x ip q p n ((p', n') :: rest) X g okv)
    (hokn : okn = 0#64 ∨ okn = 1#64)
    (r1 : v1.m.core.rip = b + 0x2b57#64) (m1 : v1.m.memory = x.m.memory) (g1 : v1.g = x.g)
    (R1 : ∀ r, r ≠ .rax → v1.m.core.read r = x.m.core.read r)
    (al1 : (v1.m.core.read .rax).setWidth 8 = okn.setWidth 8) (f1 : v1.m.core.fsBase = x.m.core.fsBase)
    (k : ∀ v, LoopAtO E W b lb kb sr sc s v (q + 8#64) p' n' rest X g okn → v.g = x.g →
      v.m.memory = storeMem x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 okn → MustQ W Q v) :
    MustQ W Q v1 := by
  have I := M.dig.cl.img
  have hb := M.dig.cl.hb
  have hroom : Room W x.m.memory (s.m.core.read .rsp) 4096 := F.body.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := c.lo
  have hKroom : ∀ a, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat + 8 → ¬ W.Kept a :=
    fun a h1 h2 => (hroom.2.2 a h1 h2).2.2
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => by by_contra hc; exact hKroom a (by omega) (by omega) ha
  have hd := F.body.done
  have hql := F.qlim
  simp only [List.length_cons] at hql
  have e28 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64).toNat = (s.m.core.read .rsp).toNat - 224 :=
    (fp_neg _ 0xd8 (by omega) (by decide) (by decide)).trans (by omega)
  have e20 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff20#64).toNat = (s.m.core.read .rsp).toNat - 232 :=
    (fp_neg _ 0xe0 (by omega) (by decide) (by decide)).trans (by omega)
  have e18 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64).toNat = (s.m.core.read .rsp).toNat - 240 :=
    (fp_neg _ 0xe8 (by omega) (by decide) (by decide)).trans (by omega)
  obtain ⟨-, -, -, -, ha1, ha2, ha3, ha4, ha5⟩ := F.args
  have hd1 : v1.g.done = none := by rw [g1]; exact hd
  have bp1 : v1.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [R1 _ (by decide)]; exact F.rbp
  have q1 : v1.m.core.read .r15 = q := by rw [R1 _ (by decide)]; exact F.r15
  -- 0x2b57
  refine step2b57c I hb hd1 (m1 ▸ F.ma) r1 (endp := q + BitVec.ofNat 64 (8 * (rest.length + 1 + 1)))
    (by rw [m1, bp1]; exact F.endp) (by rw [q1]; exact ult_more hql) ?_
  intro v2 r2 m2 g2 R2 q2 f2
  have hm2 : v2.m.memory = x.m.memory := m2.trans m1
  have hd2 : v2.g.done = none := by rw [g2]; exact hd1
  have bp2 : v2.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [R2 _ (by decide) (by decide)]; exact bp1
  have ax2 : ((v2.m.core.read .rax).setWidth 8).setWidth 64 = okn := by
    rw [R2 _ (by decide) (by decide), al1]; rcases hokn with rfl | rfl <;> rfl
  have q2' : v2.m.core.read .r15 = q + 8#64 := by rw [q2, q1]
  -- the store at rbp - 0xd8
  have hKs : Keeps (fun a => a ≠ (s.m.core.read .rsp).toNat - 224) x.m.memory
      (storeMem x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 okn) :=
    storeMem_keeps fun a ha => by rw [e28]; omega
  have hKK : Keeps W.Kept x.m.memory
      (storeMem x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 okn) :=
    hKs.mono fun a ha he => hKroom a (by omega) (by omega) (he ▸ ha)
  refine step2b6b I hb hd2 (hm2 ▸ F.ma) r2
    (by rw [hm2, bp2, e28]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)) (nm := p') ?_ ?_
  · rw [hm2, bp2, ax2, q2', loadN_keeps hKK (fun j hj => Or.inr (Or.inl (ha2 j hj)))]; exact ha1
  intro v3 r3 m3 g3 R3 n3 f3
  have hm3 : v3.m.memory = storeMem x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 okn := by
    rw [m3, hm2, bp2, ax2]
  have hd3 : v3.g.done = none := by rw [g3]; exact hd2
  have bp3 : v3.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by rw [R3 _ (by decide)]; exact bp2
  have hIs : Keeps (ImgW b) x.m.memory v3.m.memory := by
    rw [hm3]; exact hKK.mono fun a ha => Or.inl (by rw [I]; exact ha.1)
  have hMA3 : ShaMainAll b v3.m.memory := F.ma.keepW hb hIs
  -- 0x2b74
  refine step2b74 I hb hd3 hMA3 r3 (dx := s.m.core.read .rsp - 8#64 + 0xffffffffffffff58#64)
    (by rw [hm3, bp3, loadN_keeps hKs (fun j hj => by rw [e20]; omega)]; exact F.dsl) ?_
  intro v4 r4 m4 g4 R4 d4 s4 i4 f4
  have hm4 : v4.m.memory = storeMem x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 okn :=
    m4.trans hm3
  have hg4 : v4.g = x.g := by rw [g4, g3, g2, g1]
  have hd4 : v4.g.done = none := by rw [hg4]; exact hd
  have hR : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .r15 → r ≠ .r12 → r ≠ .rdx → r ≠ .rsi →
      v4.m.core.read r = x.m.core.read r := fun r h1 h2 h3 h4 h5 h6 => by
    rw [R4 r h5 h6 h2, R3 r h4, R2 r h2 h3, R1 r h1]
  have hfs4 : v4.m.core.fsBase = x.m.core.fsBase := by rw [f4, f3, f2, f1]
  have hK4 : Keeps (fun a => a ≠ (s.m.core.read .rsp).toNat - 224) x.m.memory v4.m.memory := hm4 ▸ hKs
  have hKK4 : Keeps W.Kept x.m.memory v4.m.memory := hm4 ▸ hKK
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [I]; exact ha)
  have hIW : ∀ m : Nat, m < 0xa188 → ∀ j, j < 8 → m + j < 0xa188 →
      W.Kept ((b + BitVec.ofNat 64 m).toNat + j) := fun m hm j hj hmj =>
    hImgK _ (by rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩)
  have hfile : ∀ f st, E.S.file x.m.memory f st → E.S.file v4.m.memory f st := fun f st hf =>
    (E.S.local_ _ _ _ _ (hK4.mono fun a ha => by
      have := E.S.foot_lo _ _ _ _ hf ha; omega) hf).1
  have hpe : ∀ acc a, v4.m.memory.permits acc a = x.m.memory.permits acc a := fun _ _ => by rw [hm4]; rfl
  obtain ⟨sto, hso, hse, hsr, hsX⟩ := F.out
  have hsp4 : v4.m.core.read .rsp = x.m.core.read .rsp := hR .rsp (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine k v4 ⟨⟨Body.freshK F.body rfl (by decide) hsp4 hfs4 hd4 hpe (hK4.mono fun a ha => by omega)
      (F.body.mem.keepW hb (hK4.mono fun a ha => by
        have := hKout a (hImgK a ha.1); omega)),
    by rw [m4]; exact hMA3,
    by rw [loadN_keeps hKK4 (fun j hj => hIW 0xa040 (by decide) j (by omega) (by omega))]; exact F.bss,
    (hKK4.permitted (fun j hj => hIW 0xa040 (by decide) j (by omega) (by omega))).2 F.bssw,
    by rw [loadN_keeps hKK4 (fun j hj => hIW 0xa160 (by decide) j (by omega) (by omega))]; exact F.hr,
    r4, by rw [hR .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact F.rbp,
    by rw [hR .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact F.rbx,
    by rw [R4 .r12 (by decide) (by decide) (by decide)]; exact n3,
    by rw [hR .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact F.r14,
    by rw [R4 .r15 (by decide) (by decide) (by decide), R3 .r15 (by decide)]; exact q2',
    hfs4.trans F.fs, by rw [hg4]; exact F.jobs, by rw [hg4]; exact F.atexit,
    by rw [loadN_keeps hKK4 (fun j hj => c.guardk j hj)]; exact F.guard,
    by rw [hK4.readBytes (fun j hj => by omega)]; exact F.guards,
    ⟨sto, ⟨hfile _ _ hso.1, hso.2⟩, hse, hsr, by rw [hg4]; exact hsX⟩,
    hfile _ _ F.err, F.vars.keepR (hKK4.mono fun a ha => ?_),
    by rw [hK4.readBytes (fun j hj => by omega)]; exact F.tag,
    by rw [hK4.readBytes (fun j hj => by omega)]; exact F.bin,
    by rw [loadN_keeps hKK4 (fun j hj => hIW 0xa178 (by decide) j (by omega) (by omega))]; exact F.len,
    ?_, ?_, ?_, ?_, ?_, ArgsAt.keep (hKK4.mono fun a h => Or.inr (Or.inl h)) ⟨ha1, ha2, ha3, ha4, ha5⟩,
    by rw [hg4]; exact F.res.mono (by simp)⟩, by rw [i4]; exact n3,
    by rw [s4, R3 .rbx (by decide), R2 .rbx (by decide) (by decide), R1 .rbx (by decide)]; exact F.rbx, d4,
    by rw [hg4]; simpa using F.res⟩ hg4 hm4
  · have := F.vars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
    rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
      simp only [VarR] at ha; omega] at this
  · rw [loadN_keeps hK4 (fun j hj => by rw [e18]; omega), F.endp, endp_succ hql, List.length_cons]
  · rw [addr_toNat (v := 8) (by omega)]; omega
  · rw [hm4]
    have h1 := loadN_store1 (m := x.m.memory) (a := s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) (v := okn)
      (by rw [e28]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega))
    rw [h1]; rcases hokn with rfl | rfl <;> rfl
  · rw [loadN_keeps hK4 (fun j hj => by rw [e20]; omega)]; exact F.dsl
  · rw [hK4.readBytes (fun j hj => by omega)]; exact F.ret

/-- **To the next operand** (`0x2c8a` → `0x2b81`), any `ok` byte 0 or 1 (K8), the ghost kept. -/
theorem loop_nextO {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {Q : PState → Prop} {x : PState} {q p p' g okv : Word} {n n' : List Byte} {rest : List (Word × List Byte)}
    {X : List Byte} (F : LoopFrO E W b lb kb sr sc s x (b + 0x2c8a#64) q p n ((p', n') :: rest) X g okv)
    (hok : okv = 0#64 ∨ okv = 1#64)
    (k : ∀ v, LoopAtO E W b lb kb sr sc s v (q + 8#64) p' n' rest X g okv → v.g = x.g →
      v.m.memory = storeMem x.m.memory (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64) 1 okv → MustQ W Q v) :
    MustQ W Q x :=
  step2c8a M.dig.cl.img M.dig.cl.hb F.body.done F.ma F.rip (ok := okv) (by rw [F.rbp]; exact F.ok)
    fun _ r1 m1 g1 R1 al1 f1 => loop_head M c F hok r1 m1 g1 R1 al1 f1 k

/-- **To the next operand** (`0x2c8a` → `0x2b81`). -/
theorem loop_next {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (M : MultiImps E R W b lb kb sc) {s : PState} (c : LoopCtx E W s)
    {Q : PState → Prop} {x : PState} {q p p' g : Word} {n n' : List Byte} {rest : List (Word × List Byte)}
    {X : List Byte} (F : LoopFr E W b lb kb sr sc s x (b + 0x2c8a#64) q p n ((p', n') :: rest) X g)
    (k : ∀ v, LoopAt E W b lb kb sr sc s v (q + 8#64) p' n' rest X g → MustQ W Q v) : MustQ W Q x :=
  loop_nextO M c F (Or.inr rfl) fun v hv _ _ => k v hv

end Silmaril.Elf.Link.Dyn.Sha256sum
