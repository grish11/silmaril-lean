module

public import Silmaril.Sim.X86.Toy.Thms
public import Silmaril.Sim.Reduce.Loop.Thms
public import Silmaril.Sim.Reduce.Toy.Defs
public import Silmaril.Sim.Reduce.Toy.SumTo.Thms
public import Silmaril.Sim.Reduce.Toy.Dbl.Thms
public import Silmaril.Machine.X86.BlockCert.Store.Thms

/-!
# The toy's `f`, decomposed: three Wasm pieces and the callees' contracts

The header is `Silmaril/Sim/Reduce/Toy/F/Thms.lean`.
-/

@[expose] public section

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State MState Byte)
open Silmaril.X86.Ext (Sz RM retire readRM writeRM aluStep)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Wasm.Logic.Hoare (HWP)

namespace Silmaril.Sim.Reduce.Toy.F
variable {H : Type} {s : Store H} {f : Frame} {σ : State}

/-- Progress of a memory load `mov r64, [m]`. -/
private theorem progressM_load {W : Win} {sz : Sz} {d : Reg} {m : Silmaril.X86.Ext.Mem} {len : Nat}
    {code : List Silmaril.Wasm.Instr} (hmem : emitMem W (.load sz d m) len = some code)
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hw : ∀ a, accessMem (.load sz d m) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.load sz d m) σ mem len = .ok σ' mem' := by
  obtain ⟨rfl, -⟩ : sz = .q ∧ plainMem m = true := by
    dsimp only [emitMem] at hmem
    unfold loadM at hmem
    split at hmem
    · assumption
    · cases hmem
  obtain ⟨B, v, -, hv, -⟩ := hM.load (hw _ rfl)
  refine ⟨{ Sz.q.write σ d (v.setWidth Sz.q.bits) with rip := σ.rip + BitVec.ofNat 64 len },
    mem, ?_⟩
  simp only [Silmaril.X86.Ext.exec, readRM, show Sz.q.bytes = 8 from rfl, hv, Option.map_some,
    retire]

/-- Progress of a memory store `mov [m], r64`. -/
private theorem progressM_store {W : Win} {sz : Sz} {dst : RM} {src : Reg} {len : Nat}
    {code : List Silmaril.Wasm.Instr} (hmem : emitMem W (.mov sz dst src) len = some code)
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hw : ∀ a, accessMem (.mov sz dst src) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.mov sz dst src) σ mem len = .ok σ' mem' := by
  dsimp only [emitMem] at hmem
  unfold storeM at hmem
  split at hmem
  · split at hmem
    · rename_i hp
      obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store hp.1 (hw _ rfl) (σ.read src)
      refine ⟨{ σ with rip := σ.rip + BitVec.ofNat 64 len }, mem', ?_⟩
      simp only [Silmaril.X86.Ext.exec, writeRM, Sz.read_q, show Sz.q.bytes = 8 from rfl]
      rw [show @BitVec.setWidth Sz.q.bits 64 (σ.read src) = σ.read src from BitVec.setWidth_eq _,
        hst]
      rfl
    · cases hmem
  · cases hmem

/-- Progress of `push r`. -/
private theorem progressM_push {W : Win} {r : Reg} {len : Nat}
    {code : List Silmaril.Wasm.Instr} (hmem : emitMem W (.push r) len = some code)
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hw : ∀ a, accessMem (.push r) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.push r) σ mem len = .ok σ' mem' := by
  have hrw : W.rw = true := by
    dsimp only [emitMem] at hmem
    split at hmem
    · assumption
    · cases hmem
  obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store hrw (hw _ rfl) (σ.read r)
  refine ⟨{ σ.write .rsp (σ.read .rsp - 8#64) with rip := σ.rip + BitVec.ofNat 64 len }, mem', ?_⟩
  simp only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some, retire]

/-- Progress of `pop r`. -/
private theorem progressM_pop {W : Win} {r : Reg} {len : Nat}
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hw : ∀ a, accessMem (.pop r) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.pop r) σ mem len = .ok σ' mem' := by
  obtain ⟨B, v, -, hv, -⟩ := hM.load (hw _ rfl)
  refine ⟨{ (σ.write .rsp (σ.read .rsp + 8#64)).write r v with
    rip := σ.rip + BitVec.ofNat 64 len }, mem, ?_⟩
  simp only [Silmaril.X86.Ext.exec, popWord_loadN hv, Option.map_some, retire]

/-- Progress of `call rel`. -/
private theorem progressM_call {W : Win} {rel : BitVec 32} {len : Nat}
    {code : List Silmaril.Wasm.Instr} (hmem : emitMem W (.call rel) len = some code)
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hw : ∀ a, accessMem (.call rel) σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.call rel) σ mem len = .ok σ' mem' := by
  have hrw : W.rw = true := by
    dsimp only [emitMem] at hmem
    split at hmem
    · assumption
    · cases hmem
  obtain ⟨ma, mi, B', mem', -, hst, -⟩ := hM.store hrw (hw _ rfl) (σ.rip + BitVec.ofNat 64 len)
  refine ⟨{ σ.write .rsp (σ.read .rsp - 8#64) with
    rip := σ.rip + BitVec.ofNat 64 len + rel.signExtend 64 }, mem', ?_⟩
  simp only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some]

/-- Progress of `ret`. -/
private theorem progressM_ret {W : Win} {len : Nat}
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hw : ∀ a, accessMem .ret σ len = some a → W.Holds a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec .ret σ mem len = .ok σ' mem' := by
  obtain ⟨B, v, -, hv, -⟩ := hM.load (hw _ rfl)
  refine ⟨{ σ.write .rsp (σ.read .rsp + 8#64) with rip := v }, mem, ?_⟩
  simp only [Silmaril.X86.Ext.exec, popWord_loadN hv]

/-- Progress of `op r64, imm32`. -/
private theorem progressM_aluI {W : Win} {sz : Sz} {op : Silmaril.X86.AluOp} {dst : RM} {imm : BitVec 32}
    {len : Nat} {code : List Silmaril.Wasm.Instr} (hmem : emitMem W (.aluI sz op dst imm) len = some code)
    (mem : Silmaril.Process.Memory) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.aluI sz op dst imm) σ mem len = .ok σ' mem' := by
  dsimp only [emitMem] at hmem
  unfold aluIM at hmem
  split at hmem
  · cases op <;> exact ⟨_, _, rfl⟩
  · cases hmem

/-- Progress of `op r64, imm8`. -/
private theorem progressM_aluI8 {W : Win} {sz : Sz} {op : Silmaril.X86.AluOp} {dst : RM} {imm : BitVec 8}
    {len : Nat} {code : List Silmaril.Wasm.Instr} (hmem : emitMem W (.aluI8 sz op dst imm) len = some code)
    (mem : Silmaril.Process.Memory) :
    ∃ σ' mem', Silmaril.X86.Ext.exec (.aluI8 sz op dst imm) σ mem len = .ok σ' mem' := by
  dsimp only [emitMem] at hmem
  unfold aluIM at hmem
  split at hmem
  · cases op <;> exact ⟨_, _, rfl⟩
  · cases hmem

/-- Progress with memory for instructions that read no flags. -/
theorem progressM_nf {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Silmaril.Wasm.Instr}
    (hc : emitM W i len = some code) (hr : Silmaril.Sim.Reduce.Loop.readsFlags i = false)
    {mem : Silmaril.Process.Memory} (hM : MemEnc s f mem W)
    (hwK : ∀ a k, access i σ len = some (a, k) → W.HoldsK k a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem' := by
  cases hmem : emitMem W i len with
  | none =>
    show ∃ σ' mem', Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem'
    cases hX : emitX i len with
    | some c =>
      obtain ⟨σ', hx⟩ := Silmaril.Sim.Reduce.Loop.progress_nf hX hr σ mem
      exact ⟨σ', mem, hx⟩
    | none =>
      have hF : emitForm W i len = some code := by simpa only [emitM, hmem, hX] using hc
      obtain ⟨-, σ₁, -, hx⟩ := emitForm_sem hF hM hwK
      exact ⟨_, _, by rw [hx]; rfl⟩
  | some c =>
    show ∃ σ' mem', Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem'
    have hw : ∀ a, accessMem i σ len = some a → W.Holds a := fun a h => hwK a 8 (access_mem h)
    cases i
    case load => exact progressM_load hmem hM hw
    case mov => exact progressM_store hmem hM hw
    case push => exact progressM_push hmem hM hw
    case pop => exact progressM_pop hM hw
    case call => exact progressM_call hmem hM hw
    case ret => exact progressM_ret hM hw
    case aluI => exact progressM_aluI hmem mem
    case aluI8 => exact progressM_aluI8 hmem mem
    all_goals cases hmem

/-- A Wasm slot. -/
abbrev Ld (B : ByteArray) (o : Nat) (v : Word) : Prop := Memory.load B o 8 = some v

/-- **The Wasm problem with memory, final bytes included.** -/
def LProblemMB (P : Profile) (host : HostSemantics H) (W : Win) (code : List Silmaril.Wasm.Instr)
    (Pre : (Reg → Word) → Word → ByteArray → Prop)
    (Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → ByteArray → Prop) : Prop :=
  ∀ (s : Store H) (f : Frame) (R : Reg → Word) (w : Word) (B : ByteArray), GRegs s f R →
    gval s f .rip = some (Val.i64 w) → wbytes s f = some B → W.size ≤ B.size → Pre R w B →
    HWP P host s f (expression code) fun s' f' o => o = .normal [] ∧
      ∀ (R' : Reg → Word) (w' : Word) (B' : ByteArray),
        (∀ r, gval s' f' (.reg r) = some (Val.i64 (R' r))) →
        gval s' f' .rip = some (Val.i64 w') → wbytes s' f' = some B' → Post R w B R' w' B'

/-- **The x86 problem with memory, final window loads included.** -/
def XLProblemMB (tab : XTab) (W : Win) (Pre : (Reg → Word) → Word → ByteArray → Prop)
    (Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → ByteArray → Prop) : Prop :=
  ∀ (σ σ' : State) (mem mem' : Silmaril.Process.Memory) (k : Nat), WinOK mem W →
    Pre σ.read σ.rip (winBytes mem W) → XRunM tab W k σ mem σ' mem' →
    WinOK mem' W ∧ ∃ B', (∀ o v, o + 8 ≤ W.size → Ld B' o v →
      Silmaril.X86.Ext.loadN mem' (W.lo + BitVec.ofNat 64 o) 8 = some v) ∧
      Post σ.read σ.rip (winBytes mem W) σ'.read σ'.rip B'

theorem reduce_loopMB {P : Profile} {host : HostSemantics H} {W : Win} {tab : XTab}
    (hs : SupportedM W tab) {Pre : (Reg → Word) → Word → ByteArray → Prop}
    {Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → ByteArray → Prop}
    (hW : LProblemMB (H := H) P host W (dispCode (compileTabM W tab)) Pre Post) :
    XLProblemMB tab W Pre Post := by
  intro σ σ' mem mem' k hwin hpre hx
  have hE := enc_encStoreM (H := H) σ mem W
  have hM := memEnc_encStoreM (H := H) (σ := σ) hwin
  obtain ⟨⟨s', f', c'⟩, hsteps, o, hexit, rfl, rfl, hE', hM'⟩ :=
    tsafe_run (xrun_twpM (P := P) (host := host) hs hx hE hM)
  have hc : c' = vals [] := hexit
  subst hc
  have hH := hW _ _ σ.read σ.rip _ hE.gregs hE.2.2.1 (wbytes_encStoreM σ mem W)
    (by rw [winBytes_size]) hpre
  obtain ⟨-, hpost⟩ := Silmaril.Wasm.Logic.Hoare.HWP.sound_vals hH hsteps
  obtain ⟨B', hB', -, h32', hlim, hk'⟩ := id hM'
  refine ⟨⟨h32', hlim, fun k hk => ?_⟩, B', fun o v ho hv => ?_,
    hpost σ'.read σ'.rip B' hE'.2.1 hE'.2.2.1 hB'⟩
  · obtain ⟨hr, hw, x, hx, -⟩ := hk' k hk
    exact ⟨hr, hw, by rw [hx]; rfl⟩
  have hto : (W.lo + BitVec.ofNat 64 o).toNat = W.lo.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨B'', v', hB'', hl, hlB⟩ := hM'.load (a := W.lo + BitVec.ofNat 64 o)
    (by simp only [Win.Holds, hto]; omega)
  rw [hB', Option.some.injEq] at hB''
  subst hB''
  rw [hto, show W.lo.toNat + o - W.lo.toNat = o by omega, hv, Option.some.injEq] at hlB
  rw [hl, hlB]

theorem readBytes_of_loadN {mem : Silmaril.Process.Memory} {a v : Word}
    (h : Silmaril.X86.Ext.loadN mem a 8 = some v) :
    mem.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  simp only [Silmaril.X86.Ext.loadN, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, rfl⟩ := h
  have hlen : bs.length = 8 := by
    unfold Silmaril.Process.Memory.readBytes Silmaril.Process.Memory.readWith at hbs
    split at hbs
    · exact Silmaril.Process.Memory.readBacking_length hbs
    · cases hbs
  have := Silmaril.X86.Ext.leBytes_leValue bs (by omega)
  rw [hlen] at this
  rw [hbs, ← Silmaril.X86.Ext.leBytes_eight, this]


open Silmaril.Sim.X86.Toy (TV toyWin st_sub_rsp st_mov_rbx_rsi st_mov_r12_rax st_mov_rdi_rbx
  st_add_rax_r12 st_add_rsp ld_same ld_keep size_keep toyWin_ok holds_sp)
open Silmaril.Wasm.Logic.Core (exec Post)

/-- `f` placed at code base `b` (the toy's layout: `f` at `b + 0x17`). Its calls leave the table
(to `sum_to` at `b`, `dbl` at `b + 0x10`): the callees are the environment's. -/
def fTab (b : Word) : XTab :=
  [(b + 0x17, .push .rbx, 1), (b + 0x18, .push .r12, 2), (b + 0x1a, .aluI8 .q .sub (.reg .rsp) 8, 4),
    (b + 0x1e, .mov .q (.reg .rbx) .rsi, 3), (b + 0x21, .call 0xffffffda, 5),
    (b + 0x26, .mov .q (.reg .r12) .rax, 3), (b + 0x29, .mov .q (.reg .rdi) .rbx, 3),
    (b + 0x2c, .call 0xffffffdf, 5),
    (b + 0x31, .alu .q .add (.reg .rax) .r12, 3), (b + 0x34, .aluI8 .q .add (.reg .rsp) 8, 4),
    (b + 0x38, .pop .r12, 2), (b + 0x3a, .pop .rbx, 1), (b + 0x3b, .ret, 1)]

theorem ctab_eq (b sp : Word) : compileTabM (toyWin sp) (fTab b) =
    [(b + 0x17, storeCode (toyWin sp) rspDown [gget (.reg .rbx)] ++ rspDown ++ [gset (.reg .rsp)] ++
        nextCode 1),
     (b + 0x18, storeCode (toyWin sp) rspDown [gget (.reg .r12)] ++ rspDown ++ [gset (.reg .rsp)] ++
        nextCode 2),
     (b + 0x1a, aluICode .sub .rsp ((8 : BitVec 8).signExtend 64) ++ nextCode 4),
     (b + 0x1e, [gget (.reg .rsi), gset (.reg .rbx)] ++ nextCode 3),
     (b + 0x21, storeCode (toyWin sp) rspDown [gget .rip, c64 (BitVec.ofNat 64 5), b64op .add] ++
        rspDown ++ [gset (.reg .rsp), gget .rip,
        c64 (BitVec.ofNat 64 5 + (0xffffffda : BitVec 32).signExtend 64), b64op .add, gset .rip]),
     (b + 0x26, [gget (.reg .rax), gset (.reg .r12)] ++ nextCode 3),
     (b + 0x29, [gget (.reg .rbx), gset (.reg .rdi)] ++ nextCode 3),
     (b + 0x2c, storeCode (toyWin sp) rspDown [gget .rip, c64 (BitVec.ofNat 64 5), b64op .add] ++
        rspDown ++ [gset (.reg .rsp), gget .rip,
        c64 (BitVec.ofNat 64 5 + (0xffffffdf : BitVec 32).signExtend 64), b64op .add, gset .rip]),
     (b + 0x31, aluCode .add .rax .r12 ++ nextCode 3),
     (b + 0x34, aluICode .add .rsp ((8 : BitVec 8).signExtend 64) ++ nextCode 4),
     (b + 0x38, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset (.reg .r12)] ++ nextCode 2),
     (b + 0x3a, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset (.reg .rbx)] ++ nextCode 1),
     (b + 0x3b, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset .rip])] := rfl

theorem supported (b sp : Word) : SupportedM (toyWin sp) (fTab b) := by
  intro e he
  simp only [fTab, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- No instruction of `f` reads the flags. -/
theorem noFlags (b : Word) : ∀ e ∈ fTab b, Silmaril.Sim.Reduce.Loop.readsFlags e.2.1 = false := by
  intro e he
  simp only [fTab, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Segment A: entry to the call of `sum_to` -/

/-- The claim at the entry `w` of `f`'s dispatcher, for a measured invariant `J`: the entry's
code evaluates to a `J k'`-store with `k' < k`, or no entry matches and `J 0` holds. -/
abbrev EntryF (b sp : Word) (f : Frame) (J : Nat → Store H → Prop) (k : Nat) (s : Store H)
    (w : Word) : Prop :=
  match lookupC (compileTabM (toyWin sp) (fTab b)) w with
  | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, J k' s'
  | none => J 0 s

/-- The cut points of segment A (entry registers `R`, entry `rsp = sp`, caller's return address
`ret` at window offset 32), with measure `k`. -/
def CPA (b sp ret : Word) (R : Reg → Word) (k : Nat) (ip ax di rsp bx r12 : Word) (B : ByteArray) :
    Prop :=
  Ld B 32 ret ∧ ax = R .rax ∧ di = R .rdi ∧ (
  (ip = b + 0x17 ∧ rsp = sp ∧ bx = R .rbx ∧ r12 = R .r12 ∧ k = 5) ∨
  (ip = b + 0x18 ∧ rsp = sp - 8 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ Ld B 24 (R .rbx) ∧ k = 4) ∨
  (ip = b + 0x1a ∧ rsp = sp - 16 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ Ld B 24 (R .rbx) ∧
    Ld B 16 (R .r12) ∧ k = 3) ∨
  (ip = b + 0x1e ∧ rsp = sp - 24 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ Ld B 24 (R .rbx) ∧
    Ld B 16 (R .r12) ∧ k = 2) ∨
  (ip = b + 0x21 ∧ rsp = sp - 24 ∧ bx = R .rsi ∧ r12 = R .r12 ∧ Ld B 24 (R .rbx) ∧
    Ld B 16 (R .r12) ∧ k = 1) ∨
  (ip = b ∧ rsp = sp - 32 ∧ bx = R .rsi ∧ r12 = R .r12 ∧ Ld B 24 (R .rbx) ∧
    Ld B 16 (R .r12) ∧ Ld B 0 (b + 0x26) ∧ k = 0))

/-- The measured invariant of segment A. -/
def JA (b sp ret : Word) (f : Frame) (R : Reg → Word) (k : Nat) (s : Store H) : Prop :=
  ∃ ip ax di rsp bx r12 zf B, TV s f R ip ax di rsp bx r12 zf B ∧ CPA b sp ret R k ip ax di rsp bx r12 B

set_option maxHeartbeats 1000000 in
/-- **Segment A, every entry** (Wasm cut points). -/
theorem entriesA (b sp ret : Word) (R : Reg → Word) (h32 : 32 ≤ sp.toNat)
    (h8 : sp.toNat + 8 ≤ 2 ^ 64) :
    ∀ k (s : Store H), JA b sp ret f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, JA b sp ret f R k' s'
      | none => JA b sp ret f R 0 s := by
  rintro k s ⟨ip, ax, di, rsp, bx, r12, zf, B, hV, hc⟩
  refine ⟨ip, hV.2.1, ?_⟩
  show EntryF b sp f (JA b sp ret f R) k s ip
  have hW : (toyWin sp).Ok := toyWin_ok h32 h8
  obtain ⟨-, -, -, -, hsp, hbx, hr12, -, -, -, -⟩ := id hV
  obtain ⟨h32m, rfl, rfl, ⟨rfl, hr, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, h24, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, h24, h16, rfl⟩ | ⟨rfl, rfl, rfl, rfl, h24, h16, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, h24, h16, rfl⟩ | ⟨rfl, rfl, rfl, rfl, h24, h16, h0, rfl⟩⟩ :
      CPA b sp ret R k ip ax di rsp bx r12 B := hc
  · -- push rbx
    show EntryF b sp f (JA b sp ret f R) _ s (b + 0x17)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.push_step hW (sp := sp) (by rw [← hr]; exact hsp) hbx
      (holds_sp h32 h8 8#64 (by decide)) (by simp only [toyWin]; bv_omega : _ = 24) 1
    refine ⟨s', he, 4, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨ld_keep hst (by omega) h32m, rfl, rfl,
      .inr (.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, ld_same hst, rfl⟩)⟩
  · -- push r12
    show EntryF b sp f (JA b sp ret f R) _ s (b + 0x18)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.push_step hW hsp hr12
      (by simp only [Win.Holds, toyWin]; bv_omega) (by simp only [toyWin]; bv_omega : _ = 16) 2
    refine ⟨s', he, 3, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨ld_keep hst (by omega) h32m, rfl, rfl, .inr (.inr (.inl ⟨by simp [BitVec.add_assoc],
      by bv_omega, rfl, rfl, ld_keep hst (by omega) h24, ld_same hst, rfl⟩))⟩
  · -- sub $8, %rsp
    show EntryF b sp f (JA b sp ret f R) _ s (b + 0x1a)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_sub_rsp hV
    refine ⟨s', he, 2, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, rfl, rfl, .inr (.inr (.inr (.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl,
      h24, h16, rfl⟩)))⟩
  · -- mov %rsi, %rbx
    show EntryF b sp f (JA b sp ret f R) _ s (b + 0x1e)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_rbx_rsi hV
    refine ⟨s', he, 1, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, rfl, rfl, .inr (.inr (.inr (.inr (.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl,
      h24, h16, rfl⟩))))⟩
  · -- call sum_to
    show EntryF b sp f (JA b sp ret f R) _ s (b + 0x21)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.call_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 0) 5 0xffffffda
      (by simp [BitVec.add_assoc] : b + 0x21 + BitVec.ofNat 64 5 = b + 0x26)
    refine ⟨s', he, 0, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨ld_keep hst (by omega) h32m, rfl, rfl, .inr (.inr (.inr (.inr (.inr ⟨by
      simp [BitVec.add_assoc], by bv_omega, rfl, rfl, ld_keep hst (by omega) h24,
      ld_keep hst (by omega) h16, ld_same hst, rfl⟩))))⟩
  · -- exit at sum_to's entry (`b` is named `ip` here)
    show EntryF ip sp f (JA ip sp ret f R) _ s ip
    simp only [EntryF, ctab_eq, lookupC, left_eq_add, BitVec.reduceEq, ite_false]
    exact ⟨_, _, _, _, _, _, _, _, hV, h32m, rfl, rfl, .inr (.inr (.inr (.inr (.inr
      ⟨rfl, rfl, rfl, rfl, h24, h16, h0, rfl⟩))))⟩


/-! ## Segment B: from `sum_to`'s return to the call of `dbl` -/

/-- The cut points of segment B (entry registers `R`, the saved slots `v16`, `v24`, `ret`). -/
def CPB (b sp ret v16 v24 : Word) (R : Reg → Word) (k : Nat) (ip ax di rsp bx r12 : Word)
    (B : ByteArray) : Prop :=
  Ld B 32 ret ∧ Ld B 24 v24 ∧ Ld B 16 v16 ∧ ax = R .rax ∧ bx = R .rbx ∧ (
  (ip = b + 0x26 ∧ rsp = sp - 24 ∧ r12 = R .r12 ∧ di = R .rdi ∧ k = 3) ∨
  (ip = b + 0x29 ∧ rsp = sp - 24 ∧ r12 = R .rax ∧ di = R .rdi ∧ k = 2) ∨
  (ip = b + 0x2c ∧ rsp = sp - 24 ∧ r12 = R .rax ∧ di = R .rbx ∧ k = 1) ∨
  (ip = b + 0x10 ∧ rsp = sp - 32 ∧ r12 = R .rax ∧ di = R .rbx ∧ Ld B 0 (b + 0x31) ∧ k = 0))

/-- The measured invariant of segment B. -/
def JB (b sp ret v16 v24 : Word) (f : Frame) (R : Reg → Word) (k : Nat) (s : Store H) : Prop :=
  ∃ ip ax di rsp bx r12 zf B, TV s f R ip ax di rsp bx r12 zf B ∧
    CPB b sp ret v16 v24 R k ip ax di rsp bx r12 B

set_option maxHeartbeats 1000000 in
/-- **Segment B, every entry.** -/
theorem entriesB (b sp ret v16 v24 : Word) (R : Reg → Word) (h32 : 32 ≤ sp.toNat)
    (h8 : sp.toNat + 8 ≤ 2 ^ 64) :
    ∀ k (s : Store H), JB b sp ret v16 v24 f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧
          ∃ k' < k, JB b sp ret v16 v24 f R k' s'
      | none => JB b sp ret v16 v24 f R 0 s := by
  rintro k s ⟨ip, ax, di, rsp, bx, r12, zf, B, hV, hc⟩
  refine ⟨ip, hV.2.1, ?_⟩
  show EntryF b sp f (JB b sp ret v16 v24 f R) k s ip
  have hW : (toyWin sp).Ok := toyWin_ok h32 h8
  obtain ⟨-, -, -, -, hsp, -, -, -, -, -, -⟩ := id hV
  obtain ⟨h32m, h24, h16, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, h0, rfl⟩⟩ :
      CPB b sp ret v16 v24 R k ip ax di rsp bx r12 B := hc
  · -- mov %rax, %r12
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_r12_rax hV
    refine ⟨s', he, 2, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, rfl, .inr (.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, rfl⟩)⟩
  · -- mov %rbx, %rdi
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := st_mov_rdi_rbx hV
    refine ⟨s', he, 1, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, rfl, .inr (.inr (.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl,
      rfl⟩))⟩
  · -- call dbl
    show EntryF b sp f (JB b sp ret v16 v24 f R) _ s (b + 0x2c)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', B', he, hst, hV'⟩ := hV.call_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 0) 5 0xffffffdf
      (by simp [BitVec.add_assoc] : b + 0x2c + BitVec.ofNat 64 5 = b + 0x31)
    refine ⟨s', he, 0, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨ld_keep hst (by omega) h32m, ld_keep hst (by omega) h24, ld_keep hst (by omega) h16, rfl,
      rfl, .inr (.inr (.inr ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl, ld_same hst, rfl⟩))⟩
  · -- exit at dbl's entry
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false]
    exact ⟨_, _, _, _, _, _, _, _, hV, h32m, h24, h16, rfl, rfl, .inr (.inr (.inr
      ⟨rfl, rfl, rfl, rfl, h0, rfl⟩))⟩

/-! ## Segment C: from `dbl`'s return to `f`'s return -/

/-- The cut points of segment C. -/
def CPC (b sp ret v16 v24 : Word) (R : Reg → Word) (k : Nat) (ip ax di rsp bx r12 : Word)
    (B : ByteArray) : Prop :=
  Ld B 32 ret ∧ Ld B 24 v24 ∧ Ld B 16 v16 ∧ di = R .rdi ∧ (
  (ip = b + 0x31 ∧ rsp = sp - 24 ∧ ax = R .rax ∧ bx = R .rbx ∧ r12 = R .r12 ∧ k = 5) ∨
  (ip = b + 0x34 ∧ rsp = sp - 24 ∧ ax = R .rax + R .r12 ∧ bx = R .rbx ∧ r12 = R .r12 ∧ k = 4) ∨
  (ip = b + 0x38 ∧ rsp = sp - 16 ∧ ax = R .rax + R .r12 ∧ bx = R .rbx ∧ k = 3) ∨
  (ip = b + 0x3a ∧ rsp = sp - 8 ∧ ax = R .rax + R .r12 ∧ bx = R .rbx ∧ r12 = v16 ∧ k = 2) ∨
  (ip = b + 0x3b ∧ rsp = sp ∧ ax = R .rax + R .r12 ∧ bx = v24 ∧ r12 = v16 ∧ k = 1) ∨
  (ip = ret ∧ rsp = sp + 8 ∧ ax = R .rax + R .r12 ∧ bx = v24 ∧ r12 = v16 ∧ k = 0))

/-- The measured invariant of segment C. -/
def JC (b sp ret v16 v24 : Word) (f : Frame) (R : Reg → Word) (k : Nat) (s : Store H) : Prop :=
  ∃ ip ax di rsp bx r12 zf B, TV s f R ip ax di rsp bx r12 zf B ∧
    CPC b sp ret v16 v24 R k ip ax di rsp bx r12 B

set_option maxHeartbeats 1000000 in
/-- **Segment C, every entry.** -/
theorem entriesC (b sp ret v16 v24 : Word) (R : Reg → Word) (h32 : 32 ≤ sp.toNat)
    (h8 : sp.toNat + 8 ≤ 2 ^ 64) (hret : 0x3c ≤ (ret - b).toNat) :
    ∀ k (s : Store H), JC b sp ret v16 v24 f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧
          ∃ k' < k, JC b sp ret v16 v24 f R k' s'
      | none => JC b sp ret v16 v24 f R 0 s := by
  rintro k s ⟨ip, ax, di, rsp, bx, r12, zf, B, hV, hc⟩
  refine ⟨ip, hV.2.1, ?_⟩
  show EntryF b sp f (JC b sp ret v16 v24 f R) k s ip
  have hW : (toyWin sp).Ok := toyWin_ok h32 h8
  obtain ⟨-, -, -, -, hsp, -, -, -, -, -, -⟩ := id hV
  have hne : ∀ c : Word, c.toNat < 0x3c → (ret = b + c) = False := fun c hc =>
    eq_false (by rintro rfl; simp at hret; omega)
  obtain ⟨h32m, h24, h16, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, hr, rfl, rfl, rfl, rfl⟩ |
    ⟨hip, rfl, rfl, rfl, rfl, rfl⟩⟩ : CPC b sp ret v16 v24 R k ip ax di rsp bx r12 B := hc
  · -- add %r12, %rax
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_add_rax_r12 hV
    refine ⟨s', he, 4, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, .inr (.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, rfl, rfl⟩)⟩
  · -- add $8, %rsp
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, zf', hV'⟩ := st_add_rsp hV
    refine ⟨s', he, 3, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, .inr (.inr (.inl ⟨by simp [BitVec.add_assoc], by bv_omega, rfl, rfl,
      rfl⟩))⟩
  · -- pop %r12
    show EntryF b sp f (JC b sp ret v16 v24 f R) _ s (b + 0x38)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.pop_r12_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 16) h16 2
    refine ⟨s', he, 2, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, .inr (.inr (.inr (.inl ⟨by simp [BitVec.add_assoc], by bv_omega,
      rfl, rfl, rfl, rfl⟩)))⟩
  · -- pop %rbx
    show EntryF b sp f (JC b sp ret _ _ f R) _ s (b + 0x3a)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.pop_rbx_step hW hsp (by simp only [Win.Holds, toyWin]; bv_omega)
      (by simp only [toyWin]; bv_omega : _ = 24) h24 1
    refine ⟨s', he, 1, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, .inr (.inr (.inr (.inr (.inl ⟨by simp [BitVec.add_assoc],
      by bv_omega, rfl, rfl, rfl, rfl⟩))))⟩
  · -- ret
    show EntryF b sp f (JC b sp ret _ _ f R) _ s (b + 0x3b)
    simp only [EntryF, ctab_eq, lookupC, add_right_inj, BitVec.reduceEq, ite_false, ite_true]
    obtain ⟨s', he, hV'⟩ := hV.ret_step hW (sp := sp) (by rw [← hr]; exact hsp)
      (by simp only [Win.Holds, toyWin]; bv_omega) (by simp only [toyWin]; bv_omega : _ = 32) h32m
    refine ⟨s', he, 0, by omega, _, _, _, _, _, _, _, _, hV', ?_⟩
    exact ⟨h32m, h24, h16, rfl, .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))))⟩
  · -- returned: no entry matches
    show EntryF b sp f (JC b sp ret _ _ f R) _ s ip
    have e23 : (ret = b + 23) = False := hne 23 (by decide)
    have e24 : (ret = b + 24) = False := hne 24 (by decide)
    have e26 : (ret = b + 26) = False := hne 26 (by decide)
    have e30 : (ret = b + 30) = False := hne 30 (by decide)
    have e33 : (ret = b + 33) = False := hne 33 (by decide)
    have e38 : (ret = b + 38) = False := hne 38 (by decide)
    have e41 : (ret = b + 41) = False := hne 41 (by decide)
    have e44 : (ret = b + 44) = False := hne 44 (by decide)
    have e49 : (ret = b + 49) = False := hne 49 (by decide)
    have e52 : (ret = b + 52) = False := hne 52 (by decide)
    have e56 : (ret = b + 56) = False := hne 56 (by decide)
    have e58 : (ret = b + 58) = False := hne 58 (by decide)
    have e59 : (ret = b + 59) = False := hne 59 (by decide)
    rw [hip]
    simp only [EntryF, ctab_eq, lookupC, e23, e24, e26, e30, e33, e38, e41, e44, e49, e52, e56, e58, e59, ite_false]
    exact ⟨_, _, _, _, _, _, _, _, hV, h32m, h24, h16, rfl, .inr (.inr (.inr (.inr (.inr
      ⟨hip, rfl, rfl, rfl, rfl, rfl⟩))))⟩

/-- **Wasm piece A** (`wasm-seg-a/f`): segment A's dispatcher entries, by cut points. -/
def EntriesA : Prop :=
  ∀ (H : Type) (f : Frame) (b sp ret : Word) (R : Reg → Word), 32 ≤ sp.toNat → sp.toNat + 8 ≤ 2 ^ 64 →
    ∀ k (s : Store H), JA b sp ret f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧ ∃ k' < k, JA b sp ret f R k' s'
      | none => JA b sp ret f R 0 s

/-- **Wasm piece B** (`wasm-seg-b/f`). -/
def EntriesB : Prop :=
  ∀ (H : Type) (f : Frame) (b sp ret v16 v24 : Word) (R : Reg → Word), 32 ≤ sp.toNat →
    sp.toNat + 8 ≤ 2 ^ 64 →
    ∀ k (s : Store H), JB b sp ret v16 v24 f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧
          ∃ k' < k, JB b sp ret v16 v24 f R k' s'
      | none => JB b sp ret v16 v24 f R 0 s

/-- **Wasm piece C** (`wasm-seg-c/f`). -/
def EntriesC : Prop :=
  ∀ (H : Type) (f : Frame) (b sp ret v16 v24 : Word) (R : Reg → Word), 32 ≤ sp.toNat →
    sp.toNat + 8 ≤ 2 ^ 64 → 0x3c ≤ (ret - b).toNat →
    ∀ k (s : Store H), JC b sp ret v16 v24 f R k s → ∃ w, gval s f .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s f [] code = some (s', f, []) ∧
          ∃ k' < k, JC b sp ret v16 v24 f R k' s'
      | none => JC b sp ret v16 v24 f R 0 s

theorem entriesA_sol : EntriesA := fun _ _ b sp ret R h32 h8 => entriesA b sp ret R h32 h8
theorem entriesB_sol : EntriesB := fun _ _ b sp ret v16 v24 R h32 h8 => entriesB b sp ret v16 v24 R h32 h8
theorem entriesC_sol : EntriesC := fun _ _ b sp ret v16 v24 R h32 h8 hr =>
  entriesC b sp ret v16 v24 R h32 h8 hr

/-! ## The three Wasm pieces of `f` (callees outside the dispatcher: the environment's) -/

theorem i64_inj' {x y : Word} (h : some (Val.i64 x) = some (Val.i64 y)) : x = y := by
  simpa using h

/-- Reading the registers of a `TV`-store. -/
theorem TV.regs {s : Store H} {f : Frame} {R R' : Reg → Word} {ip ax di rsp bx r12 zf : Word}
    {B : ByteArray} (h : TV s f R ip ax di rsp bx r12 zf B)
    (hR : ∀ r, gval s f (.reg r) = some (Val.i64 (R' r))) :
    R' .rax = ax ∧ R' .rdi = di ∧ R' .rsp = rsp ∧ R' .rbx = bx ∧ R' .r12 = r12 ∧
      ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsp → r ≠ .rbx → r ≠ .r12 → R' r = R r := by
  obtain ⟨-, -, h2, h3, h4, h5, h6, -, h8, -, -⟩ := h
  refine ⟨i64_inj' ((hR _).symm.trans h2), i64_inj' ((hR _).symm.trans h3),
    i64_inj' ((hR _).symm.trans h4), i64_inj' ((hR _).symm.trans h5),
    i64_inj' ((hR _).symm.trans h6), fun r a b c d e => i64_inj' ((hR _).symm.trans (h8 r a b c d e))⟩

/-- The initial `TV` of a store holding registers `R`. -/
theorem TV.init {s : Store H} {f : Frame} {R : Reg → Word} {w : Word} {B : ByteArray}
    (hG : GRegs s f R) (hw : gval s f .rip = some (Val.i64 w)) (hB : wbytes s f = some B)
    (hsz : 40 ≤ B.size) : ∃ zf, TV s f R w (R .rax) (R .rdi) (R .rsp) (R .rbx) (R .r12) zf B := by
  obtain ⟨hl, hr, -, -, ⟨bz, hz⟩, -, -⟩ := hG
  exact ⟨_, hl, hw, hr _, hr _, hr _, hr _, hr _, hz, fun r _ _ _ _ _ => hr r, hB, hsz⟩

/-- The registers but `rax rdi rsp rbx r12` are unchanged. -/
def Others (R R' : Reg → Word) : Prop :=
  ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsp → r ≠ .rbx → r ≠ .r12 → R' r = R r

def PreA (b sp ret : Word) (R : Reg → Word) (w : Word) (B : ByteArray) : Prop :=
  w = b + 0x17 ∧ R .rsp = sp ∧ Ld B 32 ret

def PostA (b sp ret : Word) (R : Reg → Word) (_w : Word) (_B : ByteArray) (R' : Reg → Word)
    (w' : Word) (B' : ByteArray) : Prop :=
  w' = b ∧ R' .rsp = sp - 32 ∧ R' .rbx = R .rsi ∧ R' .r12 = R .r12 ∧ R' .rax = R .rax ∧
    R' .rdi = R .rdi ∧ Others R R' ∧ Ld B' 32 ret ∧ Ld B' 24 (R .rbx) ∧ Ld B' 16 (R .r12) ∧
    Ld B' 0 (b + 0x26)

def PreB (b sp ret v16 v24 : Word) (R : Reg → Word) (w : Word) (B : ByteArray) : Prop :=
  w = b + 0x26 ∧ R .rsp = sp - 24 ∧ Ld B 32 ret ∧ Ld B 24 v24 ∧ Ld B 16 v16

def PostB (b sp ret v16 v24 : Word) (R : Reg → Word) (_w : Word) (_B : ByteArray)
    (R' : Reg → Word) (w' : Word) (B' : ByteArray) : Prop :=
  w' = b + 0x10 ∧ R' .rsp = sp - 32 ∧ R' .r12 = R .rax ∧ R' .rdi = R .rbx ∧ R' .rax = R .rax ∧
    R' .rbx = R .rbx ∧ Others R R' ∧ Ld B' 32 ret ∧ Ld B' 24 v24 ∧ Ld B' 16 v16 ∧
    Ld B' 0 (b + 0x31)

def PreC (b sp ret v16 v24 : Word) (R : Reg → Word) (w : Word) (B : ByteArray) : Prop :=
  w = b + 0x31 ∧ R .rsp = sp - 24 ∧ Ld B 32 ret ∧ Ld B 24 v24 ∧ Ld B 16 v16

def PostC (sp ret v16 v24 : Word) (R : Reg → Word) (_w : Word) (_B : ByteArray)
    (R' : Reg → Word) (w' : Word) (_B' : ByteArray) : Prop :=
  w' = ret ∧ R' .rsp = sp + 8 ∧ R' .rax = R .rax + R .r12 ∧ R' .rbx = v24 ∧ R' .r12 = v16 ∧
    R' .rdi = R .rdi ∧ Others R R'

variable {P : Profile} {host : HostSemantics H}

/-- **Piece A**: segment A of `f`'s dispatcher (Wasm). -/
theorem pieceA (hEA : EntriesA) (b sp ret : Word) (h32 : 32 ≤ sp.toNat) (h8 : sp.toNat + 8 ≤ 2 ^ 64) :
    LProblemMB (H := H) P host (toyWin sp) (dispCode (compileTabM (toyWin sp) (fTab b)))
      (PreA b sp ret) (PostA b sp ret) := by
  intro s f R w B hG hw hB hsz ⟨hw', hsp, hret⟩
  obtain ⟨zf, hV⟩ := TV.init hG hw hB hsz
  have hJ : JA b sp ret f R 5 s := ⟨_, _, _, _, _, _, _, _, hV, hret, rfl, rfl,
    .inl ⟨hw', hsp, rfl, rfl, rfl⟩⟩
  refine Silmaril.Sim.X86.Loop.dispatch_hwp _ (fun s => ∃ k, JA b sp ret f R k s) _ ?_ ⟨_, hJ⟩
  rintro s' ⟨k, hk⟩
  obtain ⟨w', hw2, hm⟩ := hEA H f b sp ret R h32 h8 k s' hk
  refine ⟨w', hw2, ?_⟩
  revert hm
  cases lookupC (compileTabM (toyWin sp) (fTab b)) w' with
  | some code =>
    rintro ⟨s'', he, k', -, hk'⟩
    exact ⟨s'', he, k', hk'⟩
  | none =>
    rintro ⟨ip, ax, di, rsp, bx, r12, zf, B', hV', h32m, rfl, rfl, hc⟩
    refine ⟨rfl, fun R' w3 B3 hR' hw3 hB3 => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := Silmaril.Sim.Reduce.Toy.F.TV.regs hV' hR'
    have hip := i64_inj' (hw3.symm.trans hV'.2.1)
    have hBB : B3 = B' := by have := hB3.symm.trans hV'.2.2.2.2.2.2.2.2.2.1; simpa using this
    subst hBB
    rcases hc with ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ |
      ⟨-, -, -, -, -, -, h⟩ | ⟨rfl, rfl, rfl, rfl, h24, h16, h0, -⟩ <;> try omega
    exact ⟨hip, e3, e4, e5, e1, e2, e6, h32m, h24, h16, h0⟩

/-- **Piece B** (Wasm). -/
theorem pieceB (hEB : EntriesB) (b sp ret v16 v24 : Word) (h32 : 32 ≤ sp.toNat) (h8 : sp.toNat + 8 ≤ 2 ^ 64) :
    LProblemMB (H := H) P host (toyWin sp) (dispCode (compileTabM (toyWin sp) (fTab b)))
      (PreB b sp ret v16 v24) (PostB b sp ret v16 v24) := by
  intro s f R w B hG hw hB hsz ⟨hw', hsp, hret, h24, h16⟩
  obtain ⟨zf, hV⟩ := TV.init hG hw hB hsz
  have hJ : JB b sp ret v16 v24 f R 3 s := ⟨_, _, _, _, _, _, _, _, hV, hret, h24, h16, rfl, rfl,
    .inl ⟨hw', hsp, rfl, rfl, rfl⟩⟩
  refine Silmaril.Sim.X86.Loop.dispatch_hwp _ (fun s => ∃ k, JB b sp ret v16 v24 f R k s) _ ?_ ⟨_, hJ⟩
  rintro s' ⟨k, hk⟩
  obtain ⟨w', hw2, hm⟩ := hEB H f b sp ret v16 v24 R h32 h8 k s' hk
  refine ⟨w', hw2, ?_⟩
  revert hm
  cases lookupC (compileTabM (toyWin sp) (fTab b)) w' with
  | some code =>
    rintro ⟨s'', he, k', -, hk'⟩
    exact ⟨s'', he, k', hk'⟩
  | none =>
    rintro ⟨ip, ax, di, rsp, bx, r12, zf, B', hV', h32m, h24', h16', rfl, rfl, hc⟩
    refine ⟨rfl, fun R' w3 B3 hR' hw3 hB3 => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := Silmaril.Sim.Reduce.Toy.F.TV.regs hV' hR'
    have hip := i64_inj' (hw3.symm.trans hV'.2.1)
    have hBB : B3 = B' := by have := hB3.symm.trans hV'.2.2.2.2.2.2.2.2.2.1; simpa using this
    subst hBB
    rcases hc with ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ |
      ⟨rfl, rfl, rfl, rfl, h0, -⟩ <;> try omega
    exact ⟨hip, e3, e5, e2, e1, e4, e6, h32m, h24', h16', h0⟩

/-- **Piece C** (Wasm). -/
theorem pieceC (hEC : EntriesC) (b sp ret v16 v24 : Word) (h32 : 32 ≤ sp.toNat) (h8 : sp.toNat + 8 ≤ 2 ^ 64)
    (hret : 0x3c ≤ (ret - b).toNat) :
    LProblemMB (H := H) P host (toyWin sp) (dispCode (compileTabM (toyWin sp) (fTab b)))
      (PreC b sp ret v16 v24) (PostC sp ret v16 v24) := by
  intro s f R w B hG hw hB hsz ⟨hw', hsp, hr, h24, h16⟩
  obtain ⟨zf, hV⟩ := TV.init hG hw hB hsz
  have hJ : JC b sp ret v16 v24 f R 5 s := ⟨_, _, _, _, _, _, _, _, hV, hr, h24, h16, rfl,
    .inl ⟨hw', hsp, rfl, rfl, rfl, rfl⟩⟩
  refine Silmaril.Sim.X86.Loop.dispatch_hwp _ (fun s => ∃ k, JC b sp ret v16 v24 f R k s) _ ?_ ⟨_, hJ⟩
  rintro s' ⟨k, hk⟩
  obtain ⟨w', hw2, hm⟩ := hEC H f b sp ret v16 v24 R h32 h8 hret k s' hk
  refine ⟨w', hw2, ?_⟩
  revert hm
  cases lookupC (compileTabM (toyWin sp) (fTab b)) w' with
  | some code =>
    rintro ⟨s'', he, k', -, hk'⟩
    exact ⟨s'', he, k', hk'⟩
  | none =>
    rintro ⟨ip, ax, di, rsp, bx, r12, zf, B', hV', -, -, -, rfl, hc⟩
    refine ⟨rfl, fun R' w3 B3 hR' hw3 _ => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := Silmaril.Sim.Reduce.Toy.F.TV.regs hV' hR'
    have hip := i64_inj' (hw3.symm.trans hV'.2.1)
    rcases hc with ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, -, h⟩ |
      ⟨-, -, -, -, -, h⟩ | ⟨rfl, rfl, rfl, rfl, rfl, -⟩ <;> try omega
    exact ⟨hip, e3, e1, e4, e5, e2, e6⟩

/-! ## Runs of the segments, and memory facts across segments and callees -/

/-- A Wasm slot of the window's bytes from an x86 load. -/
theorem ld_of_loadN (σ0 : State) {mem : Silmaril.Process.Memory} {W : Win} (hW : WinOK mem W) {o : Nat} {v : Word}
    (ho : o + 8 ≤ W.size) (h : Silmaril.X86.Ext.loadN mem (W.lo + BitVec.ofNat 64 o) 8 = some v) :
    Ld (winBytes mem W) o v := by
  have hM := memEnc_encStoreM (H := Nat) (σ := σ0) hW
  obtain ⟨-, hlim, -⟩ := hW
  have hto : (W.lo + BitVec.ofNat 64 o).toNat = W.lo.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨B, v', hB, hl, hlB⟩ := hM.load (a := W.lo + BitVec.ofNat 64 o)
    (by simp only [Win.Holds, hto]; omega)
  rw [wbytes_encStoreM, Option.some.injEq] at hB
  subst hB
  rw [h, Option.some.injEq] at hl
  subst hl
  rw [hto, show W.lo.toNat + o - W.lo.toNat = o by omega] at hlB
  exact hlB

/-- A memory that a callee did not write keeps its loads. -/
theorem loadN_keep {mem mem' : Silmaril.Process.Memory} (hw : mem.WritesWithin mem' fun _ => False)
    {a v : Word} (h : Silmaril.X86.Ext.loadN mem a 8 = some v) : Silmaril.X86.Ext.loadN mem' a 8 = some v := by
  simp only [Silmaril.X86.Ext.loadN] at h ⊢
  rw [hw.readBytes (fun _ _ h => h)]; exact h

/-- A memory that a callee did not write keeps the window. -/
theorem winOK_keep {mem mem' : Silmaril.Process.Memory} {W : Win}
    (hw : mem.WritesWithin mem' fun _ => False) (h : WinOK mem W) : WinOK mem' W := by
  obtain ⟨h1, h2, h4⟩ := h
  refine ⟨h1, h2, fun k hk => ?_⟩
  obtain ⟨hr, hwr, hs⟩ := h4 k hk
  rw [hw.permits, hw.permits, hw.2 _ (fun h => h)]
  exact ⟨hr, hwr, hs⟩

/-- The toy's code, loaded at `b` outside the window, decodes to `fTab b`. -/
theorem tabAt_of_loaded {mem : Silmaril.Process.Memory} {b sp : Word}
    (hl : Silmaril.X86.Ext.Loaded mem b Silmaril.Sim.Reduce.Toy.code) (h32 : 32 ≤ sp.toNat)
    (hdisj : b.toNat + 0x3c ≤ sp.toNat - 32 ∨ sp.toNat + 8 ≤ b.toNat) :
    TabAtM mem (toyWin sp) (fTab b) := by
  have hout : ∀ o len : Nat, o + len ≤ 0x3c → ∀ j < len,
      ¬ (toyWin sp).Mem ((b + BitVec.ofNat 64 o).toNat + j) := by
    intro o len hol j hj hm
    have hbo : (b + BitVec.ofNat 64 o).toNat = b.toNat + o :=
      hl.toNat_add (by simp [Silmaril.Sim.Reduce.Toy.code]; omega)
    have hsp : (sp - 32).toNat = sp.toNat - 32 := by bv_omega
    simp only [Win.Mem, toyWin, hbo, hsp] at hm
    omega
  have hf : ∀ o len : Nat, 0 < len → o + len ≤ 0x3c →
      mem.fetchBytes (b + BitVec.ofNat 64 o).toNat len =
        some ((Silmaril.Sim.Reduce.Toy.code.drop o).take len) := by
    intro o len hp hol
    rw [hl.toNat_add (by simp [Silmaril.Sim.Reduce.Toy.code]; omega)]
    exact hl.fetchBytes_sub hp (by simp [Silmaril.Sim.Reduce.Toy.code]; omega)
  show ∀ e ∈ fTab b, _
  simp only [fTab, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, hf 23 1 (by decide) (by decide), by decide, hout 23 1 (by decide)⟩
  · exact ⟨_, hf 24 2 (by decide) (by decide), by decide, hout 24 2 (by decide)⟩
  · exact ⟨_, hf 26 4 (by decide) (by decide), by decide, hout 26 4 (by decide)⟩
  · exact ⟨_, hf 30 3 (by decide) (by decide), by decide, hout 30 3 (by decide)⟩
  · exact ⟨_, hf 33 5 (by decide) (by decide), by decide, hout 33 5 (by decide)⟩
  · exact ⟨_, hf 38 3 (by decide) (by decide), by decide, hout 38 3 (by decide)⟩
  · exact ⟨_, hf 41 3 (by decide) (by decide), by decide, hout 41 3 (by decide)⟩
  · exact ⟨_, hf 44 5 (by decide) (by decide), by decide, hout 44 5 (by decide)⟩
  · exact ⟨_, hf 49 3 (by decide) (by decide), by decide, hout 49 3 (by decide)⟩
  · exact ⟨_, hf 52 4 (by decide) (by decide), by decide, hout 52 4 (by decide)⟩
  · exact ⟨_, hf 56 2 (by decide) (by decide), by decide, hout 56 2 (by decide)⟩
  · exact ⟨_, hf 58 1 (by decide) (by decide), by decide, hout 58 1 (by decide)⟩
  · exact ⟨_, hf 59 1 (by decide) (by decide), by decide, hout 59 1 (by decide)⟩

variable {P : Profile} {host : HostSemantics H}

/-- Progress of `f`'s instructions (none reads the flags). -/
theorem fprog (b sp : Word) : ∀ σ mem i n, True → lookupI (fTab b) σ.rip = some (i, n) →
    (∃ s : Store Nat, MemEnc s encFrameM mem (toyWin sp)) →
    (∀ a k, access i σ n = some (a, k) → (toyWin sp).HoldsK k a) → (emitM (toyWin sp) i n).isSome →
    ∃ σ₁ mem₁, Silmaril.X86.Ext.exec i σ mem n = .ok σ₁ mem₁ ∧ True := by
  intro σ mem i n _ hl ⟨s, hM⟩ hw hs
  obtain ⟨code, hc⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨σ₁, mem₁, hx⟩ := progressM_nf hc (noFlags b _ (lookupI_mem hl)) hM hw
  exact ⟨σ₁, mem₁, hx, trivial⟩

/-! ## Composition: `f`'s pieces with the callees' contracts -/

open Silmaril.Machine.X86 Silmaril.Sim.Reduce.Toy in
theorem retOf_eq {core : State} {memory : Silmaril.Process.Memory} {x : Word}
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) : Open.retOf core memory = x := by
  simp [Open.retOf, h, Silmaril.X86.wordOfBytes?_encodeWords]

open Silmaril.Machine.X86 in
theorem abiEntry_of {core : State} {memory : Silmaril.Process.Memory} {x : Word}
    (al : (core.read .rsp).toNat % 16 = 8)
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) : FnContract.AbiEntry core memory :=
  ⟨al, by rw [retOf_eq h]; exact h⟩

/-- A segment of `f`: run existence (Wasm ranking + progress) and its post (Wasm piece). -/
theorem segment {b sp : Word} (_h32 : 32 ≤ sp.toNat) (_h8 : sp.toNat + 8 ≤ 2 ^ 64)
    {J : Nat → Store Nat → Prop}
    (hent : ∀ k s, J k s → ∃ w, gval s encFrameM .rip = some (Val.i64 w) ∧
      match lookupC (compileTabM (toyWin sp) (fTab b)) w with
      | some code => ∃ s', exec s encFrameM [] code = some (s', encFrameM, []) ∧ ∃ k' < k, J k' s'
      | none => J 0 s)
    {Pre : (Reg → Word) → Word → ByteArray → Prop}
    {Post : (Reg → Word) → Word → ByteArray → (Reg → Word) → Word → ByteArray → Prop}
    (hW : LProblemMB (H := Nat) Silmaril.Wasm.Logic.Hoare.detP (fun _ _ _ _ => False) (toyWin sp)
      (dispCode (compileTabM (toyWin sp) (fTab b))) Pre Post)
    {σ : State} {mem : Silmaril.Process.Memory} (hwin : WinOK mem (toyWin sp))
    (hpre : Pre σ.read σ.rip (winBytes mem (toyWin sp)))
    (hJ : ∀ zf, TV (encStoreM (H := Nat) σ mem (toyWin sp)) encFrameM σ.read σ.rip (σ.read .rax)
      (σ.read .rdi) (σ.read .rsp) (σ.read .rbx) (σ.read .r12) zf (winBytes mem (toyWin sp)) →
      ∃ k, J k (encStoreM σ mem (toyWin sp)))
    (htab : TabAtM mem (toyWin sp) (fTab b)) :
    ∃ (n : Nat) (σ' : State) (mem' : Silmaril.Process.Memory),
      Silmaril.Machine.Execution.run Silmaril.Machine.X86.Open.step n ⟨σ, mem⟩ = some ⟨σ', mem'⟩ ∧
      mem.WritesWithin mem' (toyWin sp).Mem ∧ WinOK mem' (toyWin sp) ∧
      ∃ B', (∀ o v, o + 8 ≤ 40 → Ld B' o v →
        Silmaril.X86.Ext.loadN mem' ((toyWin sp).lo + BitVec.ofNat 64 o) 8 = some v) ∧
        Post σ.read σ.rip (winBytes mem (toyWin sp)) σ'.read σ'.rip B' := by
  have hE := enc_encStoreM (H := Nat) σ mem (toyWin sp)
  have hM := memEnc_encStoreM (H := Nat) (σ := σ) hwin
  obtain ⟨zf, hV⟩ := TV.init hE.gregs hE.2.2.1 (wbytes_encStoreM σ mem _)
    (by rw [winBytes_size]; rfl)
  obtain ⟨k, hk⟩ := hJ zf hV
  obtain ⟨n, σ', mem', hx⟩ := xrun_existsM (supported b sp) J
    (fun k s hk w code hw hc => by
      obtain ⟨w', hw', hm⟩ := hent k s hk
      rw [hw, Option.some.injEq, val_i64_inj] at hw'
      subst hw'
      rw [hc] at hm
      exact hm)
    (fun _ => True) (fprog b sp) k _ σ mem hk hE hM trivial
  obtain ⟨hwin', B', hag, hpost⟩ := reduce_loopMB (supported b sp) hW σ σ' mem mem' n hwin hpre hx
  obtain ⟨hrun, hww⟩ := run_of_xrunM (supported b sp) hx htab
  exact ⟨n, σ', mem', hrun, hww, hwin', B', hag, hpost⟩

open Silmaril.Machine.X86 in
/-- **The toy ISA goal for `f`, decomposed**: `f`'s three Wasm pieces (segments of its dispatcher;
the calls leave the dispatcher) composed with the **already solved callee contracts**
`isa_sumTo` and `isa_dbl` (assume-guarantee at the ISA level). -/
theorem isa_f_of (hA : EntriesA) (hB : EntriesB) (hC : EntriesC)
    (hsum : Silmaril.Sim.Reduce.Toy.isaGoal .sumTo)
    (hdbl : Silmaril.Sim.Reduce.Toy.isaGoal .dbl) : Silmaril.Sim.Reduce.Toy.isaGoal .f := by
  intro base
  rintro ⟨σ, mem⟩ - habi hent
  simp only [Open9.isa, Silmaril.Sim.Reduce.Toy.spec, Silmaril.Sim.Reduce.Toy.Entered] at habi hent ⊢
  obtain ⟨⟨hload, hrip⟩, hwin, h32, h8, hdisj, hret⟩ := hent
  have hripf : σ.rip = base + 0x17 := hrip
  have hcode : ∀ i < Silmaril.Sim.Reduce.Toy.code.length,
      ¬ (toyWin (σ.read .rsp)).Mem (base.toNat + i) := by
    intro i hi hm
    have hsp : (σ.read .rsp - 32).toNat = (σ.read .rsp).toNat - 32 := by bv_omega
    simp only [Silmaril.Sim.Reduce.Toy.code, List.length_cons, List.length_nil, Win.Mem, toyWin, hsp]
      at hi hm
    omega
  have htab0 : TabAtM mem (toyWin (σ.read .rsp)) (fTab base) := tabAt_of_loaded hload h32 hdisj
  have hlo : ∀ o : Nat, (toyWin (σ.read .rsp)).lo + BitVec.ofNat 64 o =
      σ.read .rsp - 32 + BitVec.ofNat 64 o := fun _ => rfl
  have hretLd : Ld (winBytes mem (toyWin (σ.read .rsp))) 32 (Open.retOf σ mem) := by
    refine ld_of_loadN σ hwin (by simp [toyWin]) ?_
    have : (toyWin (σ.read .rsp)).lo + BitVec.ofNat 64 32 = σ.read .rsp := by
      simp [toyWin]
    rw [this]; exact Silmaril.Sim.X86.Toy.loadN_of_readBytes habi.returnAddress
  -- segment A
  obtain ⟨n1, σ1, mem1, hrun1, hww1, hwin1, B1, hag1, hA⟩ :=
    segment h32 h8 (J := JA base (σ.read .rsp) (Open.retOf σ mem) encFrameM σ.read)
      (fun k s hk => hA Nat encFrameM base _ _ σ.read h32 h8 k s hk) (pieceA hA base _ _ h32 h8) hwin
      ⟨hripf, rfl, hretLd⟩
      (fun zf hV => ⟨5, _, _, _, _, _, _, _, _, hV, hretLd, rfl, rfl, .inl ⟨hripf, rfl, rfl, rfl, rfl⟩⟩)
      htab0
  obtain ⟨e1rip, e1rsp, e1rbx, e1r12, e1rax, e1rdi, e1oth, l1_32, l1_24, l1_16, l1_0⟩ := hA
  -- callee `sum_to`
  have hrb1 : mem1.readBytes (σ1.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [base + 0x26]) := by
    rw [e1rsp]; refine readBytes_of_loadN ?_
    simpa [toyWin] using hag1 0 _ (by decide) l1_0
  obtain ⟨⟨σ2, mem2⟩, hr2, res2⟩ := hsum base ⟨σ1, mem1⟩ trivial
    (abiEntry_of (by rw [e1rsp]; have := habi.aligned; bv_omega) hrb1)
    ⟨Silmaril.Machine.X86.BlockCert.loaded_of_writesWithin hload hww1 hcode, by rw [e1rip]; simp; rfl⟩
  obtain ⟨-, ⟨pc2, st2, cs2⟩, fr2, po2⟩ := res2
  simp only at pc2 st2 cs2 fr2 po2
  have pc2' : σ2.rip = base + 0x26 := pc2.trans (retOf_eq hrb1)
  have hwin2 : WinOK mem2 (toyWin (σ.read .rsp)) := winOK_keep fr2 hwin1
  have ld2 : ∀ o v, o + 8 ≤ 40 → Ld B1 o v → Ld (winBytes mem2 (toyWin (σ.read .rsp))) o v :=
    fun o v ho h => ld_of_loadN σ2 hwin2 ho (loadN_keep fr2 (hag1 o v ho h))
  have e2rsp : σ2.read .rsp = σ.read .rsp - 24 := by rw [st2, e1rsp]; bv_omega
  have htab2 : TabAtM mem2 (toyWin (σ.read .rsp)) (fTab base) := (htab0.preserve hww1).preserve (fr2.mono fun _ h => h.elim)
  -- segment B
  obtain ⟨n3, σ3, mem3, hrun3, hww3, hwin3, B3, hag3, hB⟩ :=
    segment h32 h8 (J := JB base (σ.read .rsp) (Open.retOf σ mem) (σ.read .r12) (σ.read .rbx)
      encFrameM σ2.read)
      (fun k s hk => hB Nat encFrameM base _ _ _ _ σ2.read h32 h8 k s hk) (pieceB hB base _ _ _ _ h32 h8) hwin2
      ⟨pc2', e2rsp, ld2 _ _ (by decide) l1_32, ld2 _ _ (by decide) l1_24, ld2 _ _ (by decide) l1_16⟩
      (fun zf hV => ⟨3, _, _, _, _, _, _, _, _, hV, ld2 _ _ (by decide) l1_32, ld2 _ _ (by decide) l1_24,
        ld2 _ _ (by decide) l1_16, rfl, rfl, .inl ⟨pc2', e2rsp, rfl, rfl, rfl⟩⟩)
      htab2
  obtain ⟨e3rip, e3rsp, e3r12, e3rdi, e3rax, e3rbx, e3oth, l3_32, l3_24, l3_16, l3_0⟩ := hB
  -- callee `dbl`
  have hrb3 : mem3.readBytes (σ3.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [base + 0x31]) := by
    rw [e3rsp]; refine readBytes_of_loadN ?_
    simpa [toyWin] using hag3 0 _ (by decide) l3_0
  have hload2 : Silmaril.X86.Ext.Loaded mem2 base Silmaril.Sim.Reduce.Toy.code :=
    Silmaril.Machine.X86.BlockCert.loaded_of_writesWithin
      (Silmaril.Machine.X86.BlockCert.loaded_of_writesWithin hload hww1 hcode) fr2 (fun _ _ h => h)
  obtain ⟨⟨σ4, mem4⟩, hr4, res4⟩ := hdbl base ⟨σ3, mem3⟩ trivial
    (abiEntry_of (by rw [e3rsp]; have := habi.aligned; bv_omega) hrb3)
    ⟨Silmaril.Machine.X86.BlockCert.loaded_of_writesWithin hload2 hww3 hcode, by rw [e3rip]; rfl⟩
  obtain ⟨-, ⟨pc4, st4, cs4⟩, fr4, po4⟩ := res4
  simp only at pc4 st4 cs4 fr4 po4
  have pc4' : σ4.rip = base + 0x31 := pc4.trans (retOf_eq hrb3)
  have hwin4 : WinOK mem4 (toyWin (σ.read .rsp)) := winOK_keep fr4 hwin3
  have ld4 : ∀ o v, o + 8 ≤ 40 → Ld B3 o v → Ld (winBytes mem4 (toyWin (σ.read .rsp))) o v :=
    fun o v ho h => ld_of_loadN σ4 hwin4 ho (loadN_keep fr4 (hag3 o v ho h))
  have e4rsp : σ4.read .rsp = σ.read .rsp - 24 := by rw [st4, e3rsp]; bv_omega
  have htab4 : TabAtM mem4 (toyWin (σ.read .rsp)) (fTab base) := (htab2.preserve hww3).preserve (fr4.mono fun _ h => h.elim)
  -- segment C
  obtain ⟨n5, σ5, mem5, hrun5, hww5, _, B5, _, hC⟩ :=
    segment h32 h8 (J := JC base (σ.read .rsp) (Open.retOf σ mem) (σ.read .r12) (σ.read .rbx)
      encFrameM σ4.read)
      (fun k s hk => hC Nat encFrameM base _ _ _ _ σ4.read h32 h8 hret k s hk) (pieceC hC base _ _ _ _ h32 h8 hret)
      hwin4
      ⟨pc4', e4rsp, ld4 _ _ (by decide) l3_32, ld4 _ _ (by decide) l3_24, ld4 _ _ (by decide) l3_16⟩
      (fun zf hV => ⟨5, _, _, _, _, _, _, _, _, hV, ld4 _ _ (by decide) l3_32, ld4 _ _ (by decide) l3_24,
        ld4 _ _ (by decide) l3_16, rfl, .inl ⟨pc4', e4rsp, rfl, rfl, rfl, rfl⟩⟩)
      htab4
  obtain ⟨e5rip, e5rsp, e5rax, e5rbx, e5r12, -, e5oth⟩ := hC
  -- the result
  have hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, σ5.read r = σ.read r := by
    intro r hr
    obtain rfl | rfl | rfl | rfl | rfl | rfl :
        r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
      simpa only [Silmaril.X86.sysv64, List.mem_cons, List.not_mem_nil, or_false] using hr
    · exact e5rbx
    · rw [e5oth _ (by decide) (by decide) (by decide) (by decide) (by decide),
        cs4 _ (by simp [Silmaril.X86.sysv64]),
        e3oth _ (by decide) (by decide) (by decide) (by decide) (by decide),
        cs2 _ (by simp [Silmaril.X86.sysv64]),
        e1oth _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · exact e5r12
    all_goals
      rw [e5oth _ (by decide) (by decide) (by decide) (by decide) (by decide),
        cs4 _ (by simp [Silmaril.X86.sysv64]),
        e3oth _ (by decide) (by decide) (by decide) (by decide) (by decide),
        cs2 _ (by simp [Silmaril.X86.sysv64]),
        e1oth _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨σ5, mem5⟩, ?_, rfl, ⟨e5rip, by rw [e5rsp]; rfl, hcs⟩, ?_, ?_⟩
  · exact (Open9.reaches_of_open ⟨n1, hrun1⟩).trans (hr2.trans
      ((Open9.reaches_of_open ⟨n3, hrun3⟩).trans (hr4.trans (Open9.reaches_of_open ⟨n5, hrun5⟩))))
  · exact (hww1.trans (fr2.mono fun _ h => h.elim)).trans
      ((hww3.trans (fr4.mono fun _ h => h.elim)).trans hww5)
  · show σ5.read .rax = _
    rw [e5rax, po4, cs4 .r12 (by simp [Silmaril.X86.sysv64]), e3r12, e3rdi, po2,
      cs2 .rbx (by simp [Silmaril.X86.sysv64]), e1rbx, e1rdi]
    exact BitVec.add_comm _ _

/-- **`isa/f` solved**, from the callees' solved contracts. -/
theorem isa_f : Silmaril.Sim.Reduce.Toy.isaGoal .f :=
  isa_f_of entriesA_sol entriesB_sol entriesC_sol Silmaril.Sim.Reduce.Toy.SumTo.isa_sumTo
    Silmaril.Sim.Reduce.Toy.Dbl.isa_dbl


end Silmaril.Sim.Reduce.Toy.F
