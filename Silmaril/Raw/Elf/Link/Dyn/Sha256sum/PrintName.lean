module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintHex
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.PrintEsc

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

theorem exec_push (r : Reg) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read .rsp - 8#64).toNat 8) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.push r))) c m l =
      .ok { c.write .rsp (c.read .rsp - 8#64) with rip := c.rip + BitVec.ofNat 64 l }
        (pushMem m (c.read .rsp) (c.read r)) := by
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem h]
  simp [Silmaril.X86.Ext.retire]

theorem exec_pop (r : Reg) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : m.readBytes (c.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.pop r))) c m l =
      .ok { (c.write .rsp (c.read .rsp + 8#64)).write r v with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.popWord, h,
    Silmaril.X86.Ext.retire]

theorem exec_loadd_rbp (dst : Reg) (c : State) (m : Memory) (l : Nat) (d : BitVec 32) (v : Word)
    (h : loadN m (c.read .rbp + d.signExtend 64) 4 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .d dst (.ofReg .rbp none d)))) c m l =
      .ok { c.write dst ((v.setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write, ofReg_addr]

theorem jmpEntry_read (u : PState) (a : Word) (r : Reg) :
    (jmpEntry u a).m.core.read r = u.m.core.read r := rfl
theorem jmpEntry_mem (u : PState) (a : Word) : (jmpEntry u a).m.memory = u.m.memory := rfl
theorem jmpEntry_g (u : PState) (a : Word) : (jmpEntry u a).g = u.g := rfl
theorem jmpEntry_fs (u : PState) (a : Word) : (jmpEntry u a).m.core.fsBase = u.m.core.fsBase := rfl

theorem eval_e_logic0 :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (0#8 : BitVec 8)) .e = some true := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN]

set_option maxRecDepth 100000 in
/-- **One listed `pop r`** (`r ≠ rsp`) with the popped word known. -/
theorem must_pop {W : World} {Q : PState → Prop} {s : PState} {base : Word}
    {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o l : Nat} {r : Reg}
    (hL : listingOk code L = true) (hlk : L.lookup o = some (.ext8 (.base (.pop r)), l))
    (hd : s.g.done = none) (hin : W.InImage s.m.core.rip.toNat) (hl : Loaded s.m.memory base code)
    (hrip : s.m.core.rip = base + BitVec.ofNat 64 o) (hr : r ≠ .rsp) {v : Word}
    (hv : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]))
    (k : ∀ t : PState, t.m.core.rip = base + BitVec.ofNat 64 (o + l) →
      t.m.core.read .rsp = s.m.core.read .rsp + 8#64 → t.m.core.read r = v →
      (∀ r', r' ≠ r → r' ≠ .rsp → t.m.core.read r' = s.m.core.read r') →
      t.m.memory = s.m.memory → t.g = s.g → t.m.core.fsBase = s.m.core.fsBase → MustQ W Q t) :
    MustQ W Q s := by
  refine must_listed hL hlk hd hin hl hrip ?_
  rw [exec_pop r _ _ _ v hv]
  simp only [WP_ok]
  refine k _ (by simp [hrip, ripadd]) (by simp [Ne.symm hr]) (by simp) (fun r' h1 h2 => by simp [h1, h2])
    rfl rfl rfl

/-- `vs` pushed in order onto the stack at `sp` (the first value at `sp - 8`). -/
def pushes (m : Memory) (sp : Word) : List Word → Memory
  | [] => m
  | v :: vs => pushes (pushMem m sp v) (sp - 8#64) vs

theorem pushes_permits (m : Memory) (sp : Word) (vs : List Word) (acc : Access) (a : Nat) :
    (pushes m sp vs).permits acc a = m.permits acc a := by
  induction vs generalizing m sp with
  | nil => rfl
  | cons v vs ih => exact (ih _ _).trans (pushMem_permits m sp v acc a)

theorem pushes_keeps (m : Memory) (sp : Word) (vs : List Word) (h : 8 * vs.length ≤ sp.toNat) :
    Keeps (fun x => x < sp.toNat - 8 * vs.length ∨ sp.toNat ≤ x) m (pushes m sp vs) := by
  induction vs generalizing m sp with
  | nil => exact Keeps.refl _ _
  | cons v vs ih =>
    simp only [List.length_cons] at h
    have e8 : (sp - 8#64).toNat = sp.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
    refine (pushMem_keeps (fun x hx => ?_)).trans ((ih (pushMem m sp v) (sp - 8#64) (by rw [e8]; omega)).mono
      fun x hx => ?_)
    · simp only [List.length_cons] at hx; rw [e8]; omega
    · simp only [List.length_cons] at hx; rw [e8]; omega

theorem pushes_read (m : Memory) (sp : Word) (vs : List Word) (h : 8 * vs.length ≤ sp.toNat)
    (hp : ∀ a, sp.toNat - 8 * vs.length ≤ a → a + 8 ≤ sp.toNat →
      m.Permitted .read a 8 ∧ m.Permitted .write a 8) :
    ∀ i (hi : i < vs.length), (pushes m sp vs).readBytes (sp.toNat - 8 * (i + 1)) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [vs[i]]) := by
  induction vs generalizing m sp with
  | nil => intro i hi; simp at hi
  | cons v vs ih =>
    simp only [List.length_cons] at h hp
    have e8 : (sp - 8#64).toNat = sp.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
    intro i hi
    cases i with
    | zero =>
      simp only [pushes, List.getElem_cons_zero]
      rw [(pushes_keeps (pushMem m sp v) (sp - 8#64) vs (by rw [e8]; omega)).readBytes
        (fun k hk => Or.inr (by rw [e8]; omega)), show sp.toNat - 8 * (0 + 1) = (sp - 8#64).toNat by rw [e8]]
      obtain ⟨h1, h2⟩ := hp (sp.toNat - 8) (by omega) (by omega)
      exact pushMem_read (by rw [e8]; exact h1) (by rw [e8]; exact h2)
    | succ i =>
      simp only [pushes, List.getElem_cons_succ]
      rw [show sp.toNat - 8 * (i + 1 + 1) = (sp - 8#64).toNat - 8 * (i + 1) by rw [e8]; omega]
      exact ih (pushMem m sp v) (sp - 8#64) (by rw [e8]; simp at hi; omega)
        (fun a h1 h2 => by
          obtain ⟨q1, q2⟩ := hp a (by rw [e8] at h1; omega) (by rw [e8] at h2; omega)
          exact ⟨pushMem_permitted.2 q1, pushMem_permitted.2 q2⟩) i (by simpa using hi)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`print_filename (name, 0)` from `main`** (`0x2c52` → `0x2c60`): with the escape flag at
`rbp - 0xf8` clear, `main` calls `print_filename` (`0x41a0`), which saves six registers, finds no
escaping requested, restores them and tail-jumps to `fputs_unlocked (name, stdout)`; that call
returns to `0x2c60` with `name` appended to `stdout` and the caller's frame intact. -/
theorem sha_printName {E : Env} {W : World} {b lb sc : Word} (I : PrintImps E W b lb sc)
    {Q : PState → Prop} {s0 u : PState} {fr n sv : Nat} {saved : List (Nat × Word)}
    (hB : Body W (ShaMemP b lb sc) s0 u fr n saved) (hrip : u.m.core.rip = b + 0x2c52#64)
    (hesc : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff08#32) 4 = some 0#64)
    (hv : StdVars E W lb u.m.memory)
    (hlo : E.S.lo + n ≤ (s0.m.core.read .rsp).toNat)
    (hfr : fr + 64 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s0.m.core.read .rsp).toNat - fr) % 16 = 0) (hrel : W.reliable = true)
    {name : List Byte} (hname : CStr u.m.memory (u.m.core.read .r12) name)
    (hnk : ∀ j < name.length + 1, W.Kept ((u.m.core.read .r12).toNat + j))
    {st : St} (hst : StdoutIs E u.m.memory st)
    (k : ∀ v st', Body W (ShaMemP b lb sc) s0 v fr n saved → v.m.core.rip = b + 0x2c60#64 →
      v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) →
      StdoutIs E v.m.memory st' → st'.err = st.err → st'.rd = st.rd → st'.eof = st.eof → st'.reading = st.reading →
      v.g.out ++ st'.buf = u.g.out ++ st.buf ++ name →
      v.g.jobs = u.g.jobs → v.g.atexit = u.g.atexit → v.g.done = none →
      (v.g.inp = u.g.inp ∧ v.g.allocs = u.g.allocs ∧ v.g.heap = u.g.heap ∧
        v.g.files = u.g.files) → v.g.err = u.g.err →
      Keeps (fun a => W.Kept a ∨ (u.m.core.read .rsp).toNat ≤ a) u.m.memory v.m.memory →
      (∀ f st'', f ≠ E.stdoutF → E.S.file u.m.memory f st'' → E.S.file v.m.memory f st'') →
      LibK E W u.m.memory v.m.memory → MustQ W Q v) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hd := hB.done
  have hroom := hB.room
  have hr1 := hroom.1
  have hu : (u.m.core.read .rsp).toNat = (s0.m.core.read .rsp).toNat - fr := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by omega)
  -- `mov esi, [rbp - 0xf8]` (the escape flag, 0); `mov rdi, r12`; `call print_filename`
  refine must_listed (o := 200) shaP_listing_ok.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.printLine (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_loadd_rbp .rsi _ _ _ _ _ hesc]
  simp only [WP_ok, ripadd, hrip]
  refine must_listed (o := 206) shaP_listing_ok.1 rfl hd (hin _ (by decide)) hB.mem.printLine
    (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun x => x.m.core.rip = b + 0x2c5b#64 ∧ x.m.core.read .rsi = 0#64 ∧
      x.m.core.read .rdi = u.m.core.read .r12 ∧ x.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, x.m.core.read r = u.m.core.read r) ∧
      x.m.memory = u.m.memory ∧ x.g = u.g ∧ x.m.core.fsBase = u.m.core.fsBase)
    ⟨rfl, by simp, by simp, by simp, fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro x ⟨hxr, hxsi, hxdi, hxsp, hxc, hxm, hxg, hxf⟩
  have hBx : Body W (ShaMemP b lb sc) s0 x fr n saved := hB.of_eq hxm hxsp hxf (by rw [hxg])
  have hdx : x.g.done = none := hBx.done
  set S := u.m.core.read .rsp with hS
  have hpw : ∀ a, S.toNat - 64 ≤ a → a + 8 ≤ S.toNat →
      x.m.memory.Permitted .read a 8 ∧ x.m.memory.Permitted .write a 8 := fun a h1 h2 => by
    rw [hxm]
    exact ⟨room_perm hroom (Or.inl rfl) (by omega) (by omega), room_perm hroom (Or.inr rfl) (by omega) (by omega)⟩
  have e8 : (S - 8#64).toNat = S.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  refine must_listed (o := 209) shaP_listing_ok.1 rfl hdx (by rw [hxr]; exact hin _ (by decide))
    hBx.mem.printLine (by rw [hxr, BitVec.add_assoc]; rfl) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by rw [hxsp, e8]; exact (hpw _ (by omega) (by omega)).2)]
  xstep [hxr]
  -- `print_filename`: six pushes and `sub rsp, 8`
  set T := x.m.core.read .rsp with hT
  have hT0 : T.toNat = S.toNat := by rw [hxsp]
  have hK : ∀ a, W.Kept a → a < T.toNat - 64 ∨ T.toNat ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hkp : ∀ vs : List Word, vs.length ≤ 8 →
      Keeps (fun a => W.Kept a ∨ T.toNat ≤ a) x.m.memory (pushes x.m.memory T vs) := fun vs hl =>
    (pushes_keeps x.m.memory T vs (by omega)).mono fun a ha => by
      rcases ha with h | h
      · rcases hK a h with h' | h' <;> omega
      · omega
  have hmP : ∀ vs : List Word, vs.length ≤ 8 → ShaMemP b lb sc (pushes x.m.memory T vs) := fun vs hl =>
    shaMemP_keep I.img I.hb _ _ hBx.mem ((hkp vs hl).mono fun a ha => Or.inl (Or.inl ha))
  have hpT : ∀ a, T.toNat - 64 ≤ a → a + 8 ≤ T.toNat →
      x.m.memory.Permitted .read a 8 ∧ x.m.memory.Permitted .write a 8 := fun a h1 h2 =>
    hpw a (by omega) (by omega)
  have f8 : (T - 8#64).toNat = T.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  have f16 : (T - 8#64 - 8#64).toNat = T.toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), f8]; omega
  have f24 : (T - 8#64 - 8#64 - 8#64).toNat = T.toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), f16]; omega
  have f32 : (T - 8#64 - 8#64 - 8#64 - 8#64).toNat = T.toNat - 32 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), f24]; omega
  have f40 : (T - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat = T.toNat - 40 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), f32]; omega
  have f48 : (T - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat = T.toNat - 48 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), f40]; omega
  have f56 : (T - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64).toNat = T.toNat - 56 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), f48]; omega
  have hpf : ∀ vs : List Word, vs.length ≤ 8 → ∀ m, m = pushes x.m.memory T vs →
      Loaded m (b + 0x41a0#64) printFilenameText := fun vs hl m hm => hm ▸ (hmP vs hl).printFilename
  refine must_listed (o := 0) shaP_listing_ok.2.2.2 rfl hdx (by simpa using hin 0x41a0 (by decide))
    (hpf [b + 11360#64] (by simp) _ (by simp only [pushes])) (by simp) ?_
  rw [exec_push .rbp _ _ _ (by simpa [f16, pushMem_permitted] using (hpT _ (by omega) (by omega)).2)]
  have t1 : W.InImage (b + 16801#64).toNat := hin 0x41a1 (by decide)
  have t2 : Loaded (pushMem (pushMem x.m.memory T (b + 11360#64)) (T - 8#64) (x.m.core.read .rbp))
      (b + 0x41a0#64) printFilenameText := hpf [b + 11360#64, x.m.core.read .rbp] (by simp) _ (by simp only [pushes])
  have t3 : b + 16801#64 = b + 0x41a0#64 + BitVec.ofNat 64 1 := by rw [BitVec.add_assoc]; rfl
  xstep []
  refine must_listed (o := 1) shaP_listing_ok.2.2.2 rfl hdx t1 t2 t3 ?_
  xstep []
  refine must_listed (o := 4) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 4) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  rw [exec_push .r15 _ _ _ (by simpa [f24, pushMem_permitted] using (hpT _ (by omega) (by omega)).2)]
  xstep []
  refine must_listed (o := 6) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 6) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  xstep []
  refine must_listed (o := 9) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 9) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  rw [exec_push .r14 _ _ _ (by simpa [f32, pushMem_permitted] using (hpT _ (by omega) (by omega)).2)]
  xstep []
  refine must_listed (o := 11) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 11) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  rw [exec_push .r13 _ _ _ (by simpa [f40, pushMem_permitted] using (hpT _ (by omega) (by omega)).2)]
  xstep []
  refine must_listed (o := 13) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 13) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  rw [exec_push .r12 _ _ _ (by simpa [f48, pushMem_permitted] using (hpT _ (by omega) (by omega)).2)]
  xstep []
  refine must_listed (o := 15) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 15) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13, x.m.core.read .r12] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  rw [exec_push .rbx _ _ _ (by simpa [f56, pushMem_permitted] using (hpT _ (by omega) (by omega)).2)]
  xstep []
  refine must_listed (o := 16) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 16) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13, x.m.core.read .r12, x.m.core.read .rbx] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  xstep []
  refine must_listed (o := 20) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 20) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13, x.m.core.read .r12, x.m.core.read .rbx] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  xstep [hxsi]
  refine must_listed (o := 23) shaP_listing_ok.2.2.2 rfl hdx (hin (0x41a0 + 23) (by decide))
    (hpf [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13, x.m.core.read .r12, x.m.core.read .rbx] (by simp) _ (by simp only [pushes])) (by rw [BitVec.add_assoc]; rfl) ?_
  xstep [eval_e_logic0]
  -- `test sil, sil; je`: no escaping (`0x4280`)
  have hV : ([b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13,
      x.m.core.read .r12, x.m.core.read .rbx] : List Word).length ≤ 8 := by simp
  refine must_gen (fun y => y.m.core.rip = b + 0x4280#64 ∧ y.m.core.read .rsp = T - 64#64 ∧
      y.m.memory = pushes x.m.memory T [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15,
        x.m.core.read .r14, x.m.core.read .r13, x.m.core.read .r12, x.m.core.read .rbx] ∧
      y.g = x.g ∧ y.m.core.fsBase = x.m.core.fsBase ∧
      y.m.core.read .rdi = x.m.core.read .rdi ∧
      (∀ r ∈ [Reg.rbx, .r12, .r13, .r14], y.m.core.read r = x.m.core.read r))
    ⟨rfl, ?_, by simp only [pushes], rfl, rfl, by simp, fun r hr => ?_⟩ ?_
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same]
    apply BitVec.eq_of_toNat_eq
    rw [sub_toNat (k := 8) (by omega) (by decide), f56, sub_toNat (k := 64) (by omega) (by decide)]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  rintro y ⟨hyr, hysp, hym, hyg, hyf, hydi, hyc⟩
  have hdy : y.g.done = none := by rw [hyg]; exact hdx
  have hmy : ShaMemP b lb sc y.m.memory := hym ▸ hmP _ hV
  have hky : Keeps (fun a => W.Kept a ∨ T.toNat ≤ a) x.m.memory y.m.memory := hym ▸ hkp _ hV
  have hvy : StdVars E W lb y.m.memory := (hxm ▸ hv).keep (hky.mono fun a ha => Or.inl ha)
  refine must_listed (o := 224) shaP_listing_ok.2.2.2 rfl hdy (by rw [hyr]; exact hin (0x41a0 + 224) (by decide))
    hmy.printFilename (by rw [hyr, BitVec.add_assoc]; rfl) ?_
  xstep [hyr, hmy.stdoutV]
  refine must_listed (o := 231) shaP_listing_ok.2.2.2 rfl hdy (hin (0x41a0 + 231) (by decide))
    hmy.printFilename (by rw [BitVec.add_assoc]; rfl) ?_
  rw [exec_loadq .rsi .rax _ _ _ E.stdoutF (by simpa using hvy.out)]
  xstep []
  refine must_listed (o := 234) shaP_listing_ok.2.2.2 rfl hdy (hin (0x41a0 + 234) (by decide))
    hmy.printFilename (by rw [BitVec.add_assoc]; rfl) ?_
  xstep []
  -- the epilogue: `add rsp, 8` and six pops
  have hrd := pushes_read x.m.memory T [b + 11360#64, x.m.core.read .rbp, x.m.core.read .r15,
      x.m.core.read .r14, x.m.core.read .r13, x.m.core.read .r12, x.m.core.read .rbx] (by simp; omega)
    (fun a h1 h2 => hpT a (by simp at h1; omega) h2)
  rw [← hym] at hrd
  have g56 : (T - 64#64 + 8#64).toNat = T.toNat - 8 * (6 + 1) := by
    rw [add_toNat (k := 8) (by rw [sub_toNat (k := 64) (by omega) (by decide)]; omega),
      sub_toNat (k := 64) (by omega) (by decide)]; omega
  refine must_pop (o := 238) shaP_listing_ok.2.2.2 rfl hdy (hin (0x41a0 + 238) (by decide))
    hmy.printFilename (by rw [BitVec.add_assoc]; rfl) (by decide)
    (by simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same, hysp]; rw [g56]; exact hrd 6 (by simp)) ?_
  intro t1 h1r h1s h1v h1o h1m h1g h1f
  have d1 : t1.g.done = none := by rw [h1g]; exact hdy
  have t1s : (t1.m.core.read .rsp).toNat = T.toNat - 8 * (5 + 1) := by
    rw [h1s]; simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same, hysp]
    rw [add_toNat (k := 8) (by rw [g56]; omega), g56]; omega
  refine must_pop (o := 239) shaP_listing_ok.2.2.2 rfl d1 (by rw [h1r, ripadd]; exact hin _ (by decide))
    (h1m ▸ hmy.printFilename) h1r (by decide) (by rw [t1s, h1m]; exact hrd 5 (by simp)) ?_
  intro t2 h2r h2s h2v h2o h2m h2g h2f
  have d2 : t2.g.done = none := by rw [h2g]; exact d1
  have t2s : (t2.m.core.read .rsp).toNat = T.toNat - 8 * (4 + 1) := by
    rw [h2s, add_toNat (k := 8) (by omega), t1s]; omega
  refine must_pop (o := 241) shaP_listing_ok.2.2.2 rfl d2 (by rw [h2r, ripadd]; exact hin _ (by decide))
    (h2m ▸ h1m ▸ hmy.printFilename) h2r (by decide) (by rw [t2s, h2m, h1m]; exact hrd 4 (by simp)) ?_
  intro t3 h3r h3s h3v h3o h3m h3g h3f
  have d3 : t3.g.done = none := by rw [h3g]; exact d2
  have t3s : (t3.m.core.read .rsp).toNat = T.toNat - 8 * (3 + 1) := by
    rw [h3s, add_toNat (k := 8) (by omega), t2s]; omega
  have m3 : t3.m.memory = y.m.memory := by rw [h3m, h2m, h1m]
  refine must_pop (o := 243) shaP_listing_ok.2.2.2 rfl d3 (by rw [h3r, ripadd]; exact hin _ (by decide))
    (m3 ▸ hmy.printFilename) h3r (by decide) (by rw [t3s, m3]; exact hrd 3 (by simp)) ?_
  intro t4 h4r h4s h4v h4o h4m h4g h4f
  have d4 : t4.g.done = none := by rw [h4g]; exact d3
  have t4s : (t4.m.core.read .rsp).toNat = T.toNat - 8 * (2 + 1) := by
    rw [h4s, add_toNat (k := 8) (by omega), t3s]; omega
  have m4 : t4.m.memory = y.m.memory := by rw [h4m, m3]
  refine must_pop (o := 245) shaP_listing_ok.2.2.2 rfl d4 (by rw [h4r, ripadd]; exact hin _ (by decide))
    (m4 ▸ hmy.printFilename) h4r (by decide) (by rw [t4s, m4]; exact hrd 2 (by simp)) ?_
  intro t5 h5r h5s h5v h5o h5m h5g h5f
  have d5 : t5.g.done = none := by rw [h5g]; exact d4
  have t5s : (t5.m.core.read .rsp).toNat = T.toNat - 8 * (1 + 1) := by
    rw [h5s, add_toNat (k := 8) (by omega), t4s]; omega
  have m5 : t5.m.memory = y.m.memory := by rw [h5m, m4]
  refine must_pop (o := 247) shaP_listing_ok.2.2.2 rfl d5 (by rw [h5r, ripadd]; exact hin _ (by decide))
    (m5 ▸ hmy.printFilename) h5r (by decide) (by rw [t5s, m5]; exact hrd 1 (by simp)) ?_
  intro t6 h6r h6s h6v h6o h6m h6g h6f
  have d6 : t6.g.done = none := by rw [h6g]; exact d5
  have t6s : (t6.m.core.read .rsp).toNat = T.toNat - 8 := by
    rw [h6s, add_toNat (k := 8) (by omega), t5s]; omega
  have m6 : t6.m.memory = y.m.memory := by rw [h6m, m5]
  have hrsp6 : t6.m.core.read .rsp = T - 8#64 := BitVec.eq_of_toNat_eq (by rw [t6s, f8])
  -- the registers after the pops
  have c6 : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t6.m.core.read r = x.m.core.read r := by
    intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h6o .rbx (by decide) (by decide), h5o .rbx (by decide) (by decide), h4o .rbx (by decide) (by decide),
        h3o .rbx (by decide) (by decide), h2o .rbx (by decide) (by decide), h1v]; rfl
    · rw [h6v]; rfl
    · rw [h6o .r12 (by decide) (by decide), h5o .r12 (by decide) (by decide), h4o .r12 (by decide) (by decide),
        h3o .r12 (by decide) (by decide), h2v]; rfl
    · rw [h6o .r13 (by decide) (by decide), h5o .r13 (by decide) (by decide), h4o .r13 (by decide) (by decide),
        h3v]; rfl
    · rw [h6o .r14 (by decide) (by decide), h5o .r14 (by decide) (by decide), h4v]; rfl
    · rw [h6o .r15 (by decide) (by decide), h5v]; rfl
  have di6 : t6.m.core.read .rdi = u.m.core.read .r12 := by
    rw [h6o .rdi (by decide) (by decide), h5o .rdi (by decide) (by decide), h4o .rdi (by decide) (by decide),
      h3o .rdi (by decide) (by decide), h2o .rdi (by decide) (by decide), h1o .rdi (by decide) (by decide)]
    simp [hydi, hxdi]
  have si6 : t6.m.core.read .rsi = E.stdoutF := by
    rw [h6o .rsi (by decide) (by decide), h5o .rsi (by decide) (by decide), h4o .rsi (by decide) (by decide),
      h3o .rsi (by decide) (by decide), h2o .rsi (by decide) (by decide), h1o .rsi (by decide) (by decide)]
    simp
  have fs6 : t6.m.core.fsBase = x.m.core.fsBase := by
    rw [h6f, h5f, h4f, h3f, h2f, h1f]; simp [hyf]
  have g6 : t6.g = u.g := by rw [h6g, h5g, h4g, h3g, h2g, h1g, hyg, hxg]
  -- the memory: `y`'s is the return address pushed on `x`'s, then the six saved registers
  have hyp : y.m.memory = pushes (pushMem x.m.memory T (b + 11360#64)) (T - 8#64)
      [x.m.core.read .rbp, x.m.core.read .r15, x.m.core.read .r14, x.m.core.read .r13,
        x.m.core.read .r12, x.m.core.read .rbx] := by rw [hym]; rfl
  have hret : y.m.memory.readBytes (T - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 11360#64]) := by
    rw [f8]; exact hrd 0 (by simp)
  have hkx : Keeps (fun a => a < T.toNat - 56 ∨ T.toNat ≤ a) x.m.memory y.m.memory := by
    rw [hym]; exact (pushes_keeps x.m.memory T _ (by simp; omega)).mono fun a ha => by simp; omega
  have hfl6 : ∀ f st'', E.S.file u.m.memory f st'' → E.S.file t6.m.memory f st'' := by
    intro f st'' hf
    rw [m6]
    refine (E.S.local_ _ _ _ _ ((hxm ▸ hkx).mono fun a ha => ?_) hf).1
    have := E.S.foot_lo _ _ _ _ hf ha
    left; omega
  have hst6 : StdoutIs E t6.m.memory st := ⟨hfl6 _ _ hst.1, hst.2⟩
  have hcs6 : CStr t6.m.memory (u.m.core.read .r12) name := by
    refine ⟨hname.1, ?_⟩
    rw [m6, (hky.trans (Keeps.refl _ _)).readBytes (fun j hj => Or.inl (hnk j hj)), hxm]
    exact hname.2
  -- the tail call `jmp fputs_unlocked`
  refine must_plt_jmp (o := 248) (so := 0x330) (pb := b + 0x23c0#64) d6 I.lz shaP_listing_ok.2.2.2 rfl
    (by rw [h6r, ripadd]; exact hin _ (by decide)) (m6 ▸ hmy.printFilename) h6r
    shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (m6 ▸ hmy.plt)
    (by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x330 + 4 + 6) + BitVec.signExtend 64 0x7876#32 =
        b + 0x9f70#64 by simp only [BitVec.add_assoc]; rfl, m6]
      exact hmy.fputs)
    I.fputs.1 I.fputs.2.1 I.fputs.2.2.1 (fun r h => (impOk_fn I.fputs _ r).1 h)
    ⟨abiEntry_of (v := b + 11360#64)
      (by rw [jmpEntry_read, t6s, hT0, hu]; omega)
      (by rw [jmpEntry_read, jmpEntry_mem, hrsp6, m6]; exact hret),
      by rw [jmpEntry_read]; exact si6, ⟨st, by rw [jmpEntry_mem]; exact hst6⟩,
      ⟨name, by rw [jmpEntry_read, jmpEntry_mem, di6]; exact hcs6⟩⟩ ?_
  rintro t ⟨hlib, hgo, hoth, happ⟩
  -- back at `0x2c60` in `main`: the frame, seen from the call's entry (return address pushed)
  have hL6 : LibK E W u.m.memory (jmpEntry t6 (lb + 0x91890#64)).m.memory := by
    rw [jmpEntry_mem, m6, ← hxm]
    exact (LibK.refl E W _).high (hkx.mono fun a ha => Or.inl (by omega))
  have hLt : LibK E W u.m.memory t.m.memory := hL6.libRet hlib fun _ _ h => h
  obtain ⟨⟨habi, hkt⟩, hfst, hspt, -⟩ := hlib
  set e := jmpEntry t6 (lb + 0x91890#64) with he
  have ersp : e.m.core.read .rsp = T - 8#64 := by rw [he, jmpEntry_read, hrsp6]
  have emem : e.m.memory = y.m.memory := by rw [he, jmpEntry_mem, m6]
  let e' : PState := ⟨⟨e.m.core, pushMem x.m.memory T (b + 11360#64)⟩, e.g⟩
  have hret' : e'.m.memory.readBytes (T - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 11360#64]) :=
    pushMem_read (hpT _ (by omega) (by omega)).1 (hpT _ (by omega) (by omega)).2
  have hpe : ∀ acc a, e.m.memory.permits acc a = e'.m.memory.permits acc a := by
    intro acc a
    rw [emem, hym, pushes_permits]; rfl
  have hk' : Keeps (fun a => (W.Kept a ∨ (e.m.core.read .rsp).toNat ≤ a) ∧ ¬ False) e'.m.memory e.m.memory := by
    rw [emem, hyp]
    refine (pushes_keeps _ _ _ (by rw [f8]; simp; omega)).mono fun a ha => ?_
    rw [ersp, f8] at ha
    simp only [List.length_cons, List.length_nil]
    rw [f8]
    rcases ha.1 with h | h
    · rcases hK a h with h' | h' <;> omega
    · omega
  have hpost : Imports.ReturnsExcept W (fun _ => False) e' t ∧ HalfPerm e' t ∧ t.g.done = none := by
    refine ⟨⟨⟨?_, habi.stack, habi.calleeSaved⟩, hk'.trans hkt⟩, fun a h1 h2 acc => ?_, hgo.2.2.1⟩
    · rw [habi.pc, retOf_of (v := b + 11360#64) (by rw [ersp, emem]; exact hret)]
      have hr2 : e'.m.memory.readBytes (e'.m.core.read .rsp).toNat 8 =
          some (Silmaril.Machine.LittleEndian.encodeWords [b + 11360#64]) := by
        show e'.m.memory.readBytes (e.m.core.read .rsp).toNat 8 = _
        rw [ersp]; exact hret'
      exact (retOf_of hr2).symm
    · rw [halfOfStack hspt a h1 h2 acc, hpe]
  obtain ⟨hBt, htrip, htrsp, htcs⟩ := body_after (shaMemP_keep I.img I.hb) hBx (by omega) hn hsv
    (e := e') (ret := b + 11360#64) rfl (by show e.m.core.read .rsp = _; rw [ersp])
    (fun r hr => by show e.m.core.read r = _; rw [he, jmpEntry_read]; exact c6 r hr)
    (by show e.m.core.fsBase = _; rw [he, jmpEntry_fs, fs6]) hpost hfst (fun _ h => h.elim) (fun _ h => h.elim)
  -- what `fputs_unlocked` wrote
  obtain ⟨st', hst', heof, hrd', hrdg, hor⟩ := (happ name (by rw [jmpEntry_read, jmpEntry_mem, di6]; exact hcs6)).1 st
    (by rw [jmpEntry_mem]; exact hst6)
  obtain ⟨hout, herr⟩ : t.g.out ++ st'.buf = u.g.out ++ st.buf ++ name ∧ st'.err = st.err := by
    rcases hor with h | ⟨hr, -⟩
    · rw [jmpEntry_g, g6] at h; exact h
    · rw [hrel] at hr; cases hr
  obtain ⟨hj, ha, hdn, hii, hie, hal, hhp, hfi⟩ := hgo
  rw [jmpEntry_g, g6] at hj ha hii hie hal hhp hfi
  refine k t st' hBt htrip (by rw [htrsp]; exact hxsp) (fun r hr => by rw [htcs r hr, hxc r hr]) hst' herr hrd' heof hrdg
    hout hj ha hdn ⟨hii, hal, hhp, hfi⟩ hie ?_ (fun f st'' hne hf => hoth f st'' (by simpa using hne) (by rw [jmpEntry_mem]; exact hfl6 f st'' hf)) hLt
  -- the caller's data
  rw [← hxm]
  refine (pushMem_keeps (sp := T) (v := b + 11360#64) fun a ha => ?_).trans
    ((hk'.trans hkt).mono fun a ha => ⟨?_, id⟩)
  · rw [f8]; rcases ha with h | h
    · rcases hK a h with h' | h' <;> omega
    · omega
  · rw [ersp, f8]; rcases ha with h | h
    · exact Or.inl h
    · right; omega

end Silmaril.Elf.Link.Dyn.Sha256sum
