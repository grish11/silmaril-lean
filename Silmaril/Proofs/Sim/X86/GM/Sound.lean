module

public import Silmaril.Proofs.Sim.X86.GM.Code
public import Silmaril.Sim.X86.G.Thms

/-!
# GM: soundness of the methods with memory

**`emitM_sound`**: if the store encodes `σ` (`Enc`) and the window of `mem` (`MemEnc`), the
instruction's memory access (if any) lies in the window, and `Ext.exec i σ mem len` retires
with `σ'`, `mem'`, then the method evaluates to a store encoding `σ'` and the window of `mem'`,
and `mem'` differs from `mem` only inside the window (`WritesWithin`, the `FnContract`
footprint form). **`emitM_holds`**: if the method evaluates, its access lies in the window (the
check passed). `emitM_shape`: not `ret`-free — but memory-free forms keep the memory, and every
form keeps defined modelled flags defined.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State AluOp)
open Silmaril.X86.Ext (Sz RM Mem Base Index Result retire readRM writeRM aluStep)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append)

variable {H : Type} {s : Store H} {f : Frame} {σ : State}

theorem wbytes_upd (s : Store H) (f : Frame) (l : Loc) (v : Val) :
    wbytes (upd s f l v) f = wbytes s f := by
  simp only [upd]
  split
  · simp [wbytes, Store.mem?, Store.setGlobal]
  · rfl

theorem MemEnc.congr {mem : Silmaril.Process.Memory} {W : Win} {s' : Store H}
    (h : MemEnc s f mem W) (he : wbytes s' f = wbytes s f) : MemEnc s' f mem W := by
  obtain ⟨B, hB, r⟩ := h; exact ⟨B, he.trans hB, r⟩

theorem enc_setMem (hE : Enc s f σ) (ma : Nat) (mi : MemInst) : Enc (s.setMem ma mi) f σ := by
  obtain ⟨hl, hr, hri, hc, hz, hs, ho⟩ := hE
  exact ⟨Layout.setMem hl ma mi, fun r => by rw [gval_setMem]; exact hr r, by rw [gval_setMem]; exact hri,
    by rw [gval_setMem]; exact hc, by rw [gval_setMem]; exact hz, by rw [gval_setMem]; exact hs,
    by rw [gval_setMem]; exact ho⟩

/-- `rip := w`. -/
theorem tail_rip (hE : Enc s f σ) (rs : List Val) (w : Word) :
    exec s f (Val.i64 w :: rs) [gset .rip] = some (upd s f .rip (Val.i64 w), f, rs) ∧
      Enc (upd s f .rip (Val.i64 w)) f { σ with rip := w } ∧
      wbytes (upd s f .rip (Val.i64 w)) f = wbytes s f :=
  ⟨by simp only [exec_cons, exec_nil, exec1_gset hE.1], hE.next { σ with rip := w } rfl rfl _ rfl,
    wbytes_upd ..⟩

/-- `rip += len`. -/
theorem tail_next (hE : Enc s f σ) (len : Nat) : ∃ s', exec s f [] (nextCode len) = some (s', f, []) ∧
    Enc s' f { σ with rip := σ.rip + BitVec.ofNat 64 len } ∧ wbytes s' f = wbytes s f := by
  refine ⟨_, ?_, (tail_rip hE [] _).2⟩
  simp only [nextCode, exec_cons, exec_nil, exec1_gget, hE.2.2.1, Option.map_some, exec1_c64,
    exec1_add, exec1_gset hE.1]

/-- `d := v` (from the stack). -/
theorem tail_reg (hE : Enc s f σ) (rs : List Val) (d : Reg) (v : Word) :
    exec s f (Val.i64 v :: rs) [gset (.reg d)] = some (upd s f (.reg d) (Val.i64 v), f, rs) ∧
      Enc (upd s f (.reg d) (Val.i64 v)) f (σ.write d v) ∧
      wbytes (upd s f (.reg d) (Val.i64 v)) f = wbytes s f :=
  ⟨by simp only [exec_cons, exec_nil, exec1_gset hE.1],
    enc_reg hE d v _ (regsAfter_write _ _ _ _ rfl) rfl rfl, wbytes_upd ..⟩

/-- The state after `op d, c` (64-bit register, immediate), RIP not advanced. -/
def aluIState (op : AluOp) (d : Reg) (c : Word) (σ : State) : State :=
  if op = .cmp then { σ with flags := Silmaril.X86.Ext.AluOp.flagsN op (σ.read d) c }
  else { σ.write d (Silmaril.X86.Ext.AluOp.resultN op (σ.read d) c) with
    flags := Silmaril.X86.Ext.AluOp.flagsN op (σ.read d) c }

theorem aluI_core (hE : Enc s f σ) (op : AluOp) (d : Reg) (c : Word) :
    ∃ s₁, exec s f [] (aluICode op d c) = some (s₁, f, []) ∧ Enc s₁ f (aluIState op d c σ) ∧
      wbytes s₁ f = wbytes s f := by
  have hl := hE.1
  have hr := hE.2.1
  cases op <;>
  · simp (maxDischargeDepth := 20) only [aluICode, carryCode, overflowCode, zeroCode, msbCode,
      notCode, aluWasm, List.cons_append, List.nil_append, exec_cons, exec_nil,
      exec1_gget, hr, hl, Layout.upd, Option.map_some, exec1_c64, exec1_add, exec1_sub, exec1_and,
      exec1_or, exec1_xor, exec1_shr63, exec1_gset, gval_upd, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left', xor_neg_one, aluIState,
      wbytes_upd]
    first
    | exact enc_flags_reg hE _ _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl
        (flagEnc_msb _) (flagEnc_msb _) (flagEnc_zero _) (flagEnc_msb _)
    | exact enc_flags_reg hE _ _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl
        flagEnc_false flagEnc_false (flagEnc_zero _) (flagEnc_msb _)
    | exact enc_flags hE _ _ _ _ _ (regsAfter_same _ _ rfl) rfl
        (flagEnc_msb _) (flagEnc_msb _) (flagEnc_zero _) (flagEnc_msb _)

theorem aluI_exec {op : AluOp} {d : Reg} {c : Word} {mem mem' : Silmaril.Process.Memory} {len : Nat}
    {σ' : State} (hx : retire (σ.rip + BitVec.ofNat 64 len)
      (aluStep .q op (.reg d) c σ mem (σ.rip + BitVec.ofNat 64 len)) = .ok σ' mem') :
    mem' = mem ∧ σ' = { aluIState op d c σ with rip := σ.rip + BitVec.ofNat 64 len } := by
  cases op <;>
    simp only [aluStep, readRM, writeRM, Sz.read_q, retire, reduceCtorEq, ite_false, ite_true,
      Option.map_some, Result.ok.injEq] at hx <;>
    obtain ⟨rfl, rfl⟩ := hx <;> exact ⟨rfl, rfl⟩

theorem exec_append_some {s : Store H} {f : Frame} {rs : List Val} {A B : List Instr}
    {r : Store H × Frame × List Val} (h : exec s f rs (A ++ B) = some r) :
    ∃ r', exec s f rs A = some r' := by
  rw [exec_append] at h
  cases e : exec s f rs A with
  | none => rw [e] at h; cases h
  | some r' => exact ⟨r', rfl⟩

/-! ## Inverting the memory methods -/

theorem some_of_ite {α : Type _} {p : Prop} [Decidable p] {x c : α}
    (h : (if p then some x else none) = some c) : p ∧ c = x := by
  split at h
  · rename_i hp
    exact ⟨hp, (Option.some.inj h).symm⟩
  · cases h

theorem storeM_some {W : Win} {sz : Sz} {dst : RM} {src : Reg} {len : Nat} {c : List Instr}
    (h : storeM W sz dst src len = some c) : ∃ m, sz = .q ∧ dst = .mem m ∧ W.rw = true ∧
      plainMem m = true ∧ c = storeCode W (addrCode m) [gget (.reg src)] ++ nextCode len := by
  unfold storeM at h
  split at h
  · obtain ⟨⟨hrw, hp⟩, rfl⟩ := some_of_ite h
    exact ⟨_, rfl, rfl, hrw, hp, rfl⟩
  · cases h

theorem aluIM_some {sz : Sz} {op : AluOp} {dst : RM} {k : Word} {len : Nat} {c : List Instr}
    (h : aluIM sz op dst k len = some c) :
    ∃ d, sz = .q ∧ dst = .reg d ∧ c = aluICode op d k ++ nextCode len := by
  unfold aluIM at h
  split at h
  · exact ⟨_, rfl, rfl, (Option.some.inj h).symm⟩
  · cases h

/-- The conclusion of `emitMem_sound`: `c` runs from the empty stack to a store encoding `σ'`
and the window of `mem'`, and `mem'` differs from `mem` only inside the window. -/
def MemStep (s : Store H) (f : Frame) (c : List Instr) (σ' : State)
    (mem mem' : Silmaril.Process.Memory) (W : Win) : Prop :=
  ∃ s', exec s f [] c = some (s', f, []) ∧ Enc s' f σ' ∧ MemEnc s' f mem' W ∧
    mem.WritesWithin mem' W.Mem

/-! ## Soundness, one form at a time -/

section
variable {W : Win} {len : Nat} {c : List Instr} {mem mem' : Silmaril.Process.Memory} {σ' : State}

theorem emitMem_sound_load {sz : Sz} {d : Reg} {m : Mem} (hmem : loadM W sz d m len = some c)
    (hE : Enc s f σ) (hM : MemEnc s f mem W)
    (hx : Silmaril.X86.Ext.exec (.load sz d m) σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem (.load sz d m) σ len = some a → W.Holds a) :
    MemStep s f c σ' mem mem' W := by
  obtain ⟨⟨rfl, hp⟩, rfl⟩ := some_of_ite hmem
  obtain ⟨v, hv, hl⟩ := exec_load hM (pure_addr hE hp (σ.rip + BitVec.ofNat 64 len)) (hw _ rfl) []
  obtain ⟨rfl, rfl⟩ : { Sz.q.write σ d (v.setWidth Sz.q.bits) with
      rip := σ.rip + BitVec.ofNat 64 len } = σ' ∧ mem = mem' := by
    simpa only [Silmaril.X86.Ext.exec, readRM, show Sz.q.bytes = 8 from rfl, hv, Option.map_some,
      retire, Result.ok.injEq] using hx
  obtain ⟨h1, hE1, hw1⟩ := tail_reg hE [] d v
  obtain ⟨s₂, h2, hE2, hw2⟩ := tail_next hE1 len
  refine ⟨s₂, ?_, by simpa using hE2, hM.congr (hw2.trans hw1),
    Silmaril.Process.Memory.WritesWithin.refl _ _⟩
  rw [exec_append, exec_append, hl]
  simp only
  rw [h1]
  exact h2

theorem emitMem_sound_store {sz : Sz} {dst : RM} {src : Reg}
    (hmem : storeM W sz dst src len = some c) (hE : Enc s f σ) (hM : MemEnc s f mem W)
    (hx : Silmaril.X86.Ext.exec (.mov sz dst src) σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem (.mov sz dst src) σ len = some a → W.Holds a) :
    MemStep s f c σ' mem mem' W := by
  obtain ⟨m, rfl, rfl, hrw, hp, rfl⟩ := storeM_some hmem
  obtain ⟨ma, mi, B', mem₁, hst, hs, hM1, hww⟩ := exec_store hM hrw
    (pure_addr hE hp (σ.rip + BitVec.ofNat 64 len)) (pure_gget (hE.2.1 src)) (hw _ rfl) []
  have hsrc : @BitVec.setWidth Sz.q.bits 64 (σ.read src) = σ.read src := BitVec.setWidth_eq _
  obtain ⟨rfl, rfl⟩ : { σ with rip := σ.rip + BitVec.ofNat 64 len } = σ' ∧ mem₁ = mem' := by
    simpa only [Silmaril.X86.Ext.exec, writeRM, Sz.read_q, show Sz.q.bytes = 8 from rfl, hsrc,
      hst, Option.map_some, retire, Result.ok.injEq] using hx
  have hE1 : Enc (s.setMem ma { mi with bytes := B' }) f σ := enc_setMem hE ma _
  obtain ⟨s₂, h2, hE2, hw2⟩ := tail_next hE1 len
  exact ⟨s₂, by rw [exec_append, hs]; exact h2, hE2, hM1.congr hw2, hww⟩

theorem emitMem_sound_push {r : Reg} (hmem : emitMem W (.push r) len = some c)
    (hE : Enc s f σ) (hM : MemEnc s f mem W)
    (hx : Silmaril.X86.Ext.exec (.push r) σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem (.push r) σ len = some a → W.Holds a) :
    MemStep s f c σ' mem mem' W := by
  obtain ⟨hrw, rfl⟩ := some_of_ite hmem
  obtain ⟨ma, mi, B', mem₁, hst, hs, hM1, hww⟩ :=
    exec_store hM hrw (pure_rspDown hE) (pure_gget (hE.2.1 r)) (hw _ rfl) []
  obtain ⟨rfl, rfl⟩ : { σ.write .rsp (σ.read .rsp - 8#64) with
      rip := σ.rip + BitVec.ofNat 64 len } = σ' ∧ mem₁ = mem' := by
    simpa only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some, retire,
      Result.ok.injEq] using hx
  have hE1 : Enc (s.setMem ma { mi with bytes := B' }) f σ := enc_setMem hE ma _
  obtain ⟨h2, hE2, hw2⟩ := tail_reg hE1 [] .rsp (σ.read .rsp - 8#64)
  obtain ⟨s₃, h3, hE3, hw3⟩ := tail_next hE2 len
  refine ⟨s₃, ?_, hE3, hM1.congr (hw3.trans hw2), hww⟩
  show exec s f [] (storeCode W rspDown [gget (.reg r)] ++ rspDown ++ [gset (.reg .rsp)] ++
    nextCode len) = some (s₃, f, [])
  rw [exec_append, exec_append, exec_append, hs]
  simp only
  rw [pure_rspDown hE1]
  simp only
  rw [h2]
  exact h3

/-- `rsp + 8`, above the popped value `v`. -/
theorem exec_rspUp (hE : Enc s f σ) (v : Word) :
    exec s f [Val.i64 v] [gget (.reg .rsp), c64 8, b64op .add] =
      some (s, f, [Val.i64 (σ.read .rsp + 8#64), Val.i64 v]) := by
  simp only [exec_cons, exec_nil, exec1_gget, hE.2.1 .rsp, Option.map_some, exec1_c64, exec1_add]
  rfl

theorem emitMem_sound_pop {r : Reg} (hmem : emitMem W (.pop r) len = some c)
    (hE : Enc s f σ) (hM : MemEnc s f mem W)
    (hx : Silmaril.X86.Ext.exec (.pop r) σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem (.pop r) σ len = some a → W.Holds a) :
    MemStep s f c σ' mem mem' W := by
  have hc : loadCode W [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
      gset (.reg .rsp), gset (.reg r)] ++ nextCode len = c := Option.some.inj hmem
  obtain ⟨v, hv, hl⟩ := exec_load hM (pure_gget (hE.2.1 .rsp)) (hw _ rfl) []
  obtain ⟨rfl, rfl⟩ : { (σ.write .rsp (σ.read .rsp + 8#64)).write r v with
      rip := σ.rip + BitVec.ofNat 64 len } = σ' ∧ mem = mem' := by
    simpa only [Silmaril.X86.Ext.exec, popWord_loadN hv, Option.map_some, retire,
      Result.ok.injEq] using hx
  obtain ⟨h1, hE1, hw1⟩ := tail_reg hE [Val.i64 v] .rsp (σ.read .rsp + 8#64)
  obtain ⟨h2, hE2, hw2⟩ := tail_reg hE1 [] r v
  obtain ⟨s₃, h3, hE3, hw3⟩ := tail_next hE2 len
  refine ⟨s₃, hc ▸ ?_, hE3, hM.congr (hw3.trans (hw2.trans hw1)),
    Silmaril.Process.Memory.WritesWithin.refl _ _⟩
  have hsplit : [gget (.reg .rsp), c64 8, b64op .add, gset (.reg .rsp), gset (.reg r)] =
      [gget (.reg .rsp), c64 8, b64op .add] ++ [gset (.reg .rsp)] ++ [gset (.reg r)] := rfl
  rw [exec_append, exec_append, hl]
  simp only
  rw [hsplit, exec_append, exec_append, exec_rspUp hE v]
  simp only
  rw [h1]
  simp only
  rw [h2]
  exact h3

/-- `rip + k`. -/
theorem exec_ripAdd (hE : Enc s f σ) (k : Word) :
    exec s f [] [gget .rip, c64 k, b64op .add] = some (s, f, [Val.i64 (σ.rip + k)]) := by
  simp only [exec_cons, exec_nil, exec1_gget, hE.2.2.1, Option.map_some, exec1_c64, exec1_add]

theorem emitMem_sound_call {rel : BitVec 32} (hmem : emitMem W (.call rel) len = some c)
    (hE : Enc s f σ) (hM : MemEnc s f mem W)
    (hx : Silmaril.X86.Ext.exec (.call rel) σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem (.call rel) σ len = some a → W.Holds a) :
    MemStep s f c σ' mem mem' W := by
  obtain ⟨hrw, rfl⟩ := some_of_ite hmem
  have hV : Pure s f [gget .rip, c64 (BitVec.ofNat 64 len), b64op .add]
      (σ.rip + BitVec.ofNat 64 len) :=
    (pure_gget hE.2.2.1).op (pure_c64 _) .add (z := σ.rip + BitVec.ofNat 64 len) rfl
  obtain ⟨ma, mi, B', mem₁, hst, hs, hM1, hww⟩ :=
    exec_store hM hrw (pure_rspDown hE) hV (hw _ rfl) []
  obtain ⟨rfl, rfl⟩ : { σ.write .rsp (σ.read .rsp - 8#64) with
      rip := σ.rip + BitVec.ofNat 64 len + rel.signExtend 64 } = σ' ∧ mem₁ = mem' := by
    simpa only [Silmaril.X86.Ext.exec, pushWord_storeN, hst, Option.map_some,
      Result.ok.injEq] using hx
  have hE1 : Enc (s.setMem ma { mi with bytes := B' }) f σ := enc_setMem hE ma _
  obtain ⟨h2, hE2, hw2⟩ := tail_reg hE1 [] .rsp (σ.read .rsp - 8#64)
  obtain ⟨h4, hE4, hw4⟩ := tail_rip hE2 [] (σ.rip + (BitVec.ofNat 64 len + rel.signExtend 64))
  refine ⟨_, ?_, by simpa [BitVec.add_assoc] using hE4, hM1.congr (hw4.trans hw2), hww⟩
  have hsplit : [gset (.reg .rsp), gget .rip, c64 (BitVec.ofNat 64 len + rel.signExtend 64),
      b64op .add, gset .rip] = [gset (.reg .rsp)] ++
      [gget .rip, c64 (BitVec.ofNat 64 len + rel.signExtend 64), b64op .add] ++ [gset .rip] := rfl
  rw [exec_append, exec_append, hs]
  simp only
  rw [pure_rspDown hE1]
  simp only
  rw [hsplit, exec_append, exec_append, h2]
  simp only
  rw [exec_ripAdd hE2]
  exact h4

theorem emitMem_sound_ret (hmem : emitMem W .ret len = some c)
    (hE : Enc s f σ) (hM : MemEnc s f mem W)
    (hx : Silmaril.X86.Ext.exec .ret σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem .ret σ len = some a → W.Holds a) :
    MemStep s f c σ' mem mem' W := by
  have hc : loadCode W [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
      gset (.reg .rsp), gset .rip] = c := Option.some.inj hmem
  obtain ⟨v, hv, hl⟩ := exec_load hM (pure_gget (hE.2.1 .rsp)) (hw _ rfl) []
  obtain ⟨rfl, rfl⟩ : { σ.write .rsp (σ.read .rsp + 8#64) with rip := v } = σ' ∧ mem = mem' := by
    simpa only [Silmaril.X86.Ext.exec, popWord_loadN hv, Result.ok.injEq] using hx
  obtain ⟨h1, hE1, hw1⟩ := tail_reg hE [Val.i64 v] .rsp (σ.read .rsp + 8#64)
  obtain ⟨h2, hE2, hw2⟩ := tail_rip hE1 [] v
  refine ⟨_, hc ▸ ?_, hE2, hM.congr (hw2.trans hw1),
    Silmaril.Process.Memory.WritesWithin.refl _ _⟩
  have hsplit : [gget (.reg .rsp), c64 8, b64op .add, gset (.reg .rsp), gset .rip] =
      [gget (.reg .rsp), c64 8, b64op .add] ++ [gset (.reg .rsp)] ++ [gset .rip] := rfl
  rw [exec_append, hl]
  simp only
  rw [hsplit, exec_append, exec_append, exec_rspUp hE v]
  simp only
  rw [h1]
  exact h2

theorem emitMem_sound_aluI {sz : Sz} {op : AluOp} {dst : RM} {n : Nat} {imm : BitVec n}
    (hmem : aluIM sz op dst (imm.signExtend 64) len = some c) (hE : Enc s f σ)
    (hM : MemEnc s f mem W)
    (hx : retire (σ.rip + BitVec.ofNat 64 len) (aluStep sz op dst (imm.signExtend sz.bits) σ mem
      (σ.rip + BitVec.ofNat 64 len)) = .ok σ' mem') :
    MemStep s f c σ' mem mem' W := by
  obtain ⟨d, rfl, rfl, rfl⟩ := aluIM_some hmem
  obtain ⟨rfl, rfl⟩ := aluI_exec hx
  obtain ⟨s₁, h1, hE1, hw1⟩ := aluI_core hE op d (imm.signExtend 64)
  have hrip : (aluIState op d (imm.signExtend 64) σ).rip = σ.rip := by
    unfold aluIState; split <;> rfl
  obtain ⟨s₂, h2, hE2, hw2⟩ := tail_next hE1 len
  exact ⟨s₂, by rw [exec_append, h1]; exact h2, by simpa [hrip] using hE2,
    hM.congr (hw2.trans hw1), Silmaril.Process.Memory.WritesWithin.refl _ _⟩

end

/-- **Soundness of the memory and stack methods.** -/
theorem emitMem_sound {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {c : List Instr}
    (hmem : emitMem W i len = some c) (hE : Enc s f σ) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) {σ' : State} {mem' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem')
    (hw : ∀ a, accessMem i σ len = some a → W.Holds a) :
    ∃ s', exec s f [] c = some (s', f, []) ∧ Enc s' f σ' ∧ MemEnc s' f mem' W ∧
      mem.WritesWithin mem' W.Mem := by
  cases i with
  | load sz d m => exact emitMem_sound_load hmem hE hM hx hw
  | mov sz dst src => exact emitMem_sound_store hmem hE hM hx hw
  | push r => exact emitMem_sound_push hmem hE hM hx hw
  | pop r => exact emitMem_sound_pop hmem hE hM hx hw
  | call rel => exact emitMem_sound_call hmem hE hM hx hw
  | ret => exact emitMem_sound_ret hmem hE hM hx hw
  | aluI8 sz op dst imm => exact emitMem_sound_aluI hmem hE hM hx
  | aluI sz op dst imm => exact emitMem_sound_aluI hmem hE hM hx
  | _ => cases hmem

end Silmaril.Sim.X86.GM
