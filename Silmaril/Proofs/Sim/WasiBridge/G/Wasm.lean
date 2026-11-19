module

public import Silmaril.Proofs.Sim.WasiBridge.G.Sim

/-!
# The simulator runs of `hello`

* `exec_movI`, `exec_movabs`: the x86 semantics of the two G forms `hello` uses.
* `wrun_ins_inv`, `wrun_sys_inv`: inversion of interaction runs at an item, from an encoded store.
* **`hello_wrun`**: every interaction run of the simulator code of `hello`, from any store
  encoding any core, with the adapter's answers, has observables
  `prefix of (msg.take k).map (wr 1) ++ [exit 0]` for some `1 ≤ k ≤ 14`.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Sim.X86.G

variable {H : Type}

/-- A register move of length `n`. -/
def movStep (σ : State) (d : Reg) (v : Word) (n : Nat) : State :=
  { σ.write d v with rip := σ.rip + BitVec.ofNat 64 n }

@[simp] theorem movStep_read (σ : State) (d r : Reg) (v : Word) (n : Nat) :
    (movStep σ d v n).read r = if r = d then v else σ.read r := State.read_write σ d r v

@[simp] theorem movStep_rip (σ : State) (d : Reg) (v : Word) (n : Nat) :
    (movStep σ d v n).rip = σ.rip + BitVec.ofNat 64 n := rfl

theorem exec_movI (d : Reg) (imm : BitVec 32) (σ : State) (m : Memory) (n : Nat) :
    Silmaril.X86.Ext.exec (.movI .q (.reg d) imm) σ m n = .ok (movStep σ d (imm.signExtend 64) n) m := by
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, movStep]

set_option linter.unusedSimpArgs false in
theorem exec_movabs (d : Reg) (imm : BitVec 64) (σ : State) (m : Memory) (n : Nat) :
    Silmaril.X86.Ext.exec (.movabs d imm) σ m n = .ok (movStep σ d imm n) m := by
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, movStep]

/-- The core after the `syscall` method with answers `v` and `r11 := w` (flags kept). -/
def sysCore (σ : State) (v w : Word) : State :=
  { ((σ.write .rax v).write .rcx (σ.rip + 2)).write .r11 w with rip := σ.rip + 2 }

@[simp] theorem sysCore_read (σ : State) (v w : Word) (r : Reg) :
    (sysCore σ v w).read r = if r = .r11 then w else if r = .rcx then σ.rip + 2 else
      if r = .rax then v else σ.read r := by
  show (((σ.write .rax v).write .rcx (σ.rip + 2)).write .r11 w).read r = _
  simp only [State.read_write]

theorem enc_sysStore_any {s : Store H} {f : Frame} {σ : State} (hE : Enc s f σ) (v w : Word) :
    Enc (sysStore s f σ.rip v w) f (sysCore σ v w) := by
  have h₁ := enc_reg hE .rax v (σ.write .rax v) (regsAfter_write _ _ _ _ rfl) rfl rfl
  have h₂ := enc_reg h₁ .rcx (σ.rip + 2) ((σ.write .rax v).write .rcx (σ.rip + 2))
    (regsAfter_write _ _ _ _ rfl) rfl rfl
  have h₃ := enc_reg h₂ .r11 w (((σ.write .rax v).write .rcx (σ.rip + 2)).write .r11 w)
    (regsAfter_write _ _ _ _ rfl) rfl rfl
  exact Enc.next h₃ (sysCore σ v w) rfl rfl _ rfl

variable {Ans : List Word → Word → Prop} {s : Store H} {f : Frame}

theorem wrun_ins_inv {i : Silmaril.X86.Ext.Instr} {n : Nat} {p : List Item} {evs : List HostEv}
    {rest : List Item} (hw : WRun Ans s f (.ins i n :: p) evs rest) {σ σ' : State} (hE : Enc s f σ)
    {m : Memory} (hx : Silmaril.X86.Ext.exec i σ m n = .ok σ' m) :
    (evs = [] ∧ rest = .ins i n :: p) ∨ ∃ s' : Store H, Enc s' f σ' ∧ WRun Ans s' f p evs rest := by
  cases hw with
  | stop => exact .inl ⟨rfl, rfl⟩
  | ins hc he hw' =>
    obtain ⟨-, s'', he', hE', -⟩ := emit_sound hc hE hx
    rw [he] at he'
    cases he'
    exact .inr ⟨_, hE', hw'⟩

theorem wrun_sys_inv {p : List Item} {evs : List HostEv} {rest : List Item}
    (hw : WRun Ans s f (.sys :: p) evs rest) {σ : State} (hE : Enc s f σ) :
    (evs = [] ∧ rest = .sys :: p) ∨ (evs = [⟨sysRegs.map σ.read, none⟩] ∧ rest = .sys :: p) ∨
      ∃ v w evs', Ans (sysRegs.map σ.read) v ∧ evs = ⟨sysRegs.map σ.read, some v⟩ :: evs' ∧
        WRun Ans (sysStore s f σ.rip v w) f p evs' rest := by
  have ha := sysArgs_enc hE
  have hr := hE.2.2.1
  cases hw with
  | stop => exact .inl ⟨rfl, rfl⟩
  | pending h => rw [ha] at h; cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  | sys h hrip hans hw' =>
    rw [ha] at h; cases h
    rw [hr] at hrip
    simp only [Option.some.injEq, val_i64_inj] at hrip
    subst hrip
    exact .inr (.inr ⟨_, _, _, hans, rfl, hw'⟩)

/-- The observables `hello` may produce for the answer `k`. -/
def helloObs (k : Nat) : List Obs := (helloMsg.take k).map (.wr 1) ++ [.exit 0]

theorem msgAddr_toNat : msgAddr.toNat = 0x402000 := rfl

/-- **Every simulator run of `hello`** has the observables of the WASI hello for some answer. -/
theorem sx14 : (14 : BitVec 32).signExtend 64 = 14#64 := by decide

theorem fd32_one : (Silmaril.Process.LPS.fd32 1#64).toNat = 1 := by decide

theorem not_atRead_nil : ¬ AtRead [] := by simp [AtRead]

/-- **Every simulator run of `hello`** has the observables of the WASI hello for some answer,
does not finish the program, and does not stop at a `read`. -/
theorem hello_wrun {mem : Memory} (hmsg : wsrc mem msgAddr 14#64 = helloMsg)
    {σ : State} (hE : Enc s f σ) {evs : List HostEv} {rest : List Item}
    (hw : WRun (S1Ans mem) s f helloItems evs rest) :
    rest ≠ [] ∧ ¬ AtRead evs ∧ ∃ k, 1 ≤ k ∧ k ≤ 14 ∧ evsObs mem evs <+: helloObs k := by
  have nil : evsObs mem [] <+: helloObs 1 := List.nil_prefix
  have hw0 : WRun (S1Ans mem) s f [.ins (.movI .q (.reg .rax) 1) 7, .ins (.movI .q (.reg .rdi) 1) 7,
      .ins (.movabs .rsi msgAddr) 10, .ins (.movI .q (.reg .rdx) 14) 7, .sys,
      .ins (.movI .q (.reg .rax) 60) 7, .ins (.movI .q (.reg .rdi) 0) 7, .sys] evs rest := hw
  rcases wrun_ins_inv hw0 hE (exec_movI _ _ _ mem 7) with ⟨he, hr⟩ | ⟨s₁, hE₁, hw⟩
  · rw [he, hr]; exact ⟨nofun, not_atRead_nil, 1, le_rfl, by omega, nil⟩
  rcases wrun_ins_inv hw hE₁ (exec_movI _ _ _ mem 7) with ⟨he, hr⟩ | ⟨s₂, hE₂, hw⟩
  · rw [he, hr]; exact ⟨nofun, not_atRead_nil, 1, le_rfl, by omega, nil⟩
  rcases wrun_ins_inv hw hE₂ (exec_movabs _ _ _ mem 10) with ⟨he, hr⟩ | ⟨s₃, hE₃, hw⟩
  · rw [he, hr]; exact ⟨nofun, not_atRead_nil, 1, le_rfl, by omega, nil⟩
  rcases wrun_ins_inv hw hE₃ (exec_movI _ _ _ mem 7) with ⟨he, hr⟩ | ⟨s₄, hE₄, hw⟩
  · rw [he, hr]; exact ⟨nofun, not_atRead_nil, 1, le_rfl, by omega, nil⟩
  rcases wrun_sys_inv hw hE₄ with ⟨he, hr⟩ | ⟨he, hr⟩ | ⟨v, w, evs₅, hans, he, hw₅⟩
  · rw [he, hr]; exact ⟨nofun, not_atRead_nil, 1, le_rfl, by omega, nil⟩
  · rw [he, hr]
    refine ⟨nofun, ?_, 1, le_rfl, by omega, ?_⟩
    · simp (config := { decide := true }) [AtRead, sysRegs]
    · simp (config := { decide := true }) [evsObs, liftEv, sysRegs]
  rw [he]
  obtain ⟨-, hv1, hv14⟩ := hans
  have hv : v.toNat ≤ 14 := by
    simpa [movStep_read, reduceCtorEq, sx14, hmsg, helloMsg] using hv14
  have hev : evsObs mem [⟨sysRegs.map (movStep (movStep (movStep (movStep σ .rax ((1 : BitVec 32).signExtend 64) 7)
      .rdi ((1 : BitVec 32).signExtend 64) 7) .rsi msgAddr 10) .rdx ((14 : BitVec 32).signExtend 64) 7).read,
      some v⟩] = (helloMsg.take v.toNat).map (.wr 1) := by
    simp (config := { decide := true }) [evsObs, liftEv, sysRegs, hmsg, sysObs, fd32_one]
  have hk : ∀ o, o <+: [Obs.exit 0] → (helloMsg.take v.toNat).map (.wr 1) ++ o <+: helloObs v.toNat :=
    fun o h => (List.prefix_append_right_inj _).2 h
  suffices h : rest ≠ [] ∧ (∀ args, evs₅.getLast? = some ⟨args, none⟩ → args.head? ≠ some 0) ∧
      evsObs mem evs₅ <+: [Obs.exit 0] by
    refine ⟨h.1, ?_, v.toNat, hv1, hv, ?_⟩
    · rintro ⟨args, h1, h2⟩
      cases evs₅ with
      | nil => exact absurd h1 (by simp)
      | cons x xs => exact h.2.1 args (by simpa using h1) h2
    · rw [evsObs_cons, hev]
      exact hk _ h.2.2
  rcases wrun_ins_inv hw₅ (enc_sysStore_any hE₄ v w) (exec_movI _ _ _ mem 7) with
    ⟨he, hr⟩ | ⟨s₆, hE₆, hw⟩
  · rw [he, hr]; exact ⟨nofun, by simp, List.nil_prefix⟩
  rcases wrun_ins_inv hw hE₆ (exec_movI _ _ _ mem 7) with ⟨he, hr⟩ | ⟨s₇, hE₇, hw⟩
  · rw [he, hr]; exact ⟨nofun, by simp, List.nil_prefix⟩
  rcases wrun_sys_inv hw hE₇ with ⟨he, hr⟩ | ⟨he, hr⟩ | ⟨v', w', evs', hans', -, -⟩
  · rw [he, hr]; exact ⟨nofun, by simp, List.nil_prefix⟩
  · rw [he, hr]
    refine ⟨nofun, ?_, ?_⟩
    · simp (config := { decide := true }) [sysRegs]
    · simp (config := { decide := true }) [evsObs, liftEv, sysRegs, sysObs]
  · exact absurd hans' (by simp (config := { decide := true }) [S1Ans, sysRegs])

end Silmaril.Sim.WasiBridge.G
