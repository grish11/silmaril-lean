module

public import Silmaril.Proofs.Sim.X86.G.Sound

/-!
# The G simulator: jumps

`emitX` adds `jcc rel8` and `jmp rel8` to `emit`. `emitX_sound`: soundness of every method
(jumps included) against `Silmaril.X86.Ext.exec`, as `emit_sound`; `emitX_shape`: the memory is
unchanged, the instruction is not `ret`, and defined modelled flags stay defined.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_append exec_nil)
open Silmaril.X86 (Reg State AluOp Flags)
open Silmaril.X86.Ext (Sz RM Cond Result writeRM readRM retire aluStep)

variable {H : Type} {s : Store H} {f : Frame} {σ : State}

theorem jcc_bits (x : BitVec 64) (t : Bool) : (0 - b64 t) &&& x = if t then x else 0 := by
  cases t
  · simp [b64]
  · rw [show (0 : BitVec 64) - b64 true = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
    rfl

/-- The flags a store's flag globals admit, as concrete flags, and the condition's value. -/
theorem cond_bits {c : Cond} {taken : Bool} (ht : c.eval σ.flags = some taken)
    {bc bz bs bo : Bool} (ac : Silmaril.X86.FlagValue.Admits σ.flags.carry bc)
    (az : Silmaril.X86.FlagValue.Admits σ.flags.zero bz)
    (as : Silmaril.X86.FlagValue.Admits σ.flags.sign bs)
    (ao : Silmaril.X86.FlagValue.Admits σ.flags.overflow bo) :
    c.holds (cflags bc (σ.flags.parity.getD false) (σ.flags.adjust.getD false) bz bs bo) =
      taken := by
  have hadm : σ.flags.Admits (cflags bc (σ.flags.parity.getD false) (σ.flags.adjust.getD false)
      bz bs bo) := by
    refine ⟨ac, ?_, ?_, az, as, ao⟩ <;>
    · rcases σ.flags with ⟨_, _ | _, _ | _, _, _, _⟩ <;>
        simp [Silmaril.X86.FlagValue.Admits, cflags]
  exact Cond.eval_sound hadm ht

theorem jcc_ok (hE : Enc s f σ) (c : Cond) {cc : List Instr} (hc : condCode c = some cc)
    (rel : BitVec 8) (len : Nat) {taken : Bool} (ht : c.eval σ.flags = some taken) :
    ∃ s', exec s f [] (jccCode cc rel len) = some (s', f, []) ∧
      Enc s' f { σ with rip := σ.rip + BitVec.ofNat 64 len +
        (if taken then rel.signExtend 64 else 0) } ∧ Frames s s' f := by
  obtain ⟨hl, hr, hri, ⟨bc, hcf, ac⟩, ⟨bz, hzf, az⟩, ⟨bs, hsf, as⟩, ⟨bo, hof, ao⟩⟩ := hE
  have hv := cond_bits ht ac az as ao
  have hce := cond_eval (rs := [Val.i64 0, Val.i64 (σ.rip + BitVec.ofNat 64 len)])
    c hc hcf hzf hsf hof (σ.flags.parity.getD false) (σ.flags.adjust.getD false)
  rw [hv] at hce
  have hE : Enc s f σ := ⟨hl, hr, hri, ⟨bc, hcf, ac⟩, ⟨bz, hzf, az⟩, ⟨bs, hsf, as⟩, ⟨bo, hof, ao⟩⟩
  refine ⟨_, ?_, hE.next { σ with rip := σ.rip + BitVec.ofNat 64 len +
    (if taken then rel.signExtend 64 else 0) } rfl rfl _ rfl, (Frames.refl s f).upd hl _ _⟩
  rw [jccCode, exec_append, exec_append]
  simp only [exec_cons, exec_nil, exec1_gget, hri, Option.map_some, exec1_add, exec1_c64]
  rw [hce]
  simp only [exec1_sub, exec1_and, exec1_add, exec1_gset hl,
    jcc_bits]

theorem jmp_ok (hE : Enc s f σ) (rel : BitVec 8) (len : Nat) :
    ∃ s', exec s f [] (jmpCode rel len) = some (s', f, []) ∧
      Enc s' f { σ with rip := σ.rip + BitVec.ofNat 64 len + rel.signExtend 64 } ∧
      Frames s s' f := by
  refine ⟨_, ?_, hE.next { σ with rip := σ.rip + BitVec.ofNat 64 len + rel.signExtend 64 } rfl
    rfl _ rfl, (Frames.refl s f).upd hE.1 _ _⟩
  simp only [jmpCode, exec_cons, exec_nil, exec1_gget, hE.2.2.1, Option.map_some, exec1_c64,
    exec1_add, exec1_gset hE.1, BitVec.add_assoc]

/-- The forms `emitX` handles beyond `emit`. -/
theorem emitX_cases {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (h : emitX i len = some code) :
    (∃ c cc rel, i = .jcc8 c rel ∧ condCode c = some cc ∧ code = jccCode cc rel len) ∨
    (∃ rel, i = .jmp8 rel ∧ code = jmpCode rel len) ∨ emit i len = some code := by
  unfold emitX at h
  split at h
  · obtain ⟨cc, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨_, _, _, rfl, hc, rfl⟩
  · exact .inr (.inl ⟨_, rfl, (Option.some.inj h).symm⟩)
  · exact .inr (.inr h)

/-- **Soundness of every method, jumps included.** -/
theorem emitX_sound {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitX i len = some code) (hE : Enc s f σ) {σ' : State} {m m' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    m' = m ∧ ∃ s', exec s f [] code = some (s', f, []) ∧ Enc s' f σ' ∧ Frames s s' f := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, hcc, rfl⟩ | ⟨rel, rfl, rfl⟩ | he
  · simp only [Silmaril.X86.Ext.exec] at hx
    cases ht : c.eval σ.flags with
    | none => simp [ht] at hx
    | some taken =>
      obtain ⟨s', he, hE', hF⟩ := jcc_ok hE c hcc rel len ht
      cases taken <;> simp only [ht, Result.ok.injEq] at hx <;> obtain ⟨rfl, rfl⟩ := hx <;>
        refine ⟨rfl, s', he, ?_, hF⟩ <;> simpa using hE'
  · simp only [Silmaril.X86.Ext.exec, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, jmp_ok hE rel len⟩
  · exact emit_sound he hE hx

/-- Every method: the memory is unchanged, the instruction is not `ret`, defined modelled flags
stay defined. -/
theorem emitX_shape {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitX i len = some code) {σ σ' : State} {m m' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    m' = m ∧ i ≠ .ret ∧ (Defined σ.flags → Defined σ'.flags) := by
  rcases emitX_cases hc with ⟨c, cc, rel, rfl, hcc, rfl⟩ | ⟨rel, rfl, rfl⟩ | he
  · simp only [Silmaril.X86.Ext.exec] at hx
    cases ht : c.eval σ.flags with
    | none => simp [ht] at hx
    | some taken =>
      cases taken <;> simp only [ht, Result.ok.injEq] at hx <;> obtain ⟨rfl, rfl⟩ := hx <;>
        exact ⟨rfl, nofun, id⟩
  · simp only [Silmaril.X86.Ext.exec, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, nofun, id⟩
  · obtain ⟨core, hcore, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨hm, -, hr, hd, -⟩ := core_shape (H := Nat) (f := {}) hcore hx
    exact ⟨hm, hr, hd⟩

end Silmaril.Sim.X86.G
