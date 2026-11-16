module

public import Silmaril.Sim.WasiBridge.Defs

/-!
# ELF ≡ WASI: first lemmas

* **`ofP1_toP1`**: the reverse adapter undoes the forward one on lifted events (within 32-bit
  descriptors and counts, exit codes below 256), the Lean image of `roundtrip.sh`;
  **`p1Obs_toP1`**: the adapter preserves observables.
* `Refines`/`Equiv` are preorders/equivalences; **`Stack.equiv`**: the per-layer equivalences of a
  stack compose to `elf ≡ wasi`; `ElfWasiEquiv.of_stack`.
* **`procRun_of_ioSafe`**: an `IoSafeN` proof (the safety judgement of
  `Silmaril.Machine.Process.IoSpec`) bounds every `ProcRun` trace, so the existing safety results
  give one inclusion of `ElfWasiEquiv`. **`helloLoop_procObs`**: every observable trace of an
  x86 `hello` runtime (`Silmaril.Wasi.Runtime.HelloLoop`, e.g. the proved 42-byte program) is a
  prefix of the image of the preview1 `hello` (`write "hi"; exit 0`).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge

open Silmaril.Wasi (WEv)
open Silmaril.Wasi.Versions.P1 (fn okAns)
open Silmaril.Process.LPS (Event Word)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.X86 (MState)

/-! ## The adapter round trip -/

/-- Events whose numbers fit the 32-bit WASI p1 encoding. -/
def SysEv.Bounded : SysEv → Prop
  | .read fd n _ => fd < 2 ^ 32 ∧ n < 2 ^ 32
  | .write fd _ k => fd < 2 ^ 32 ∧ k < 2 ^ 32
  | .exit code => code < 256

theorem bytesOf_bytesV (bs : List (BitVec 8)) : Silmaril.Wasi.bytesOf (Silmaril.Wasi.bytesV bs) = bs := by
  simp [Silmaril.Wasi.bytesOf, Silmaril.Wasi.bytesV, List.filterMap_map]

theorem fn_write_ne_read : fn "fd_write" ≠ fn "fd_read" := by decide
theorem fn_exit_ne_write : fn "proc_exit" ≠ fn "fd_write" := by decide

set_option linter.unusedSimpArgs false in
/-- **WASI → syscall undoes syscall → WASI.** -/
theorem ofP1_toP1 (e : SysEv) (h : e.Bounded) : (toP1 e).flatMap ofP1 = [e] := by
  cases e with
  | read fd n data =>
    obtain ⟨hf, hn⟩ := h
    simp [toP1, ofP1, okAns, Silmaril.Wasi.okV, bytesOf_bytesV, fn_write_ne_read.symm,
      Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hn]
    omega
  | write fd data k =>
    obtain ⟨hf, hk⟩ := h
    simp [toP1, ofP1, okAns, Silmaril.Wasi.okV, bytesOf_bytesV, Nat.mod_eq_of_lt hf,
      Nat.mod_eq_of_lt hk]
    omega
  | exit code =>
    have : code % 256 < 2 ^ 32 := by omega
    have h' : code < 256 := h
    simp [toP1, ofP1, Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h']
    omega

/-- **The adapter preserves observables.** -/
theorem p1Obs_toP1 (e : SysEv) (h : e.Bounded) : (toP1 e).flatMap p1Obs = sysObs e := by
  rw [show (toP1 e).flatMap p1Obs = ((toP1 e).flatMap ofP1).flatMap sysObs by
    rw [List.flatMap_assoc]; rfl, ofP1_toP1 e h]
  simp

/-! ## Refinement and equivalence -/

theorem Refines.refl (A : List Obs → Prop) : Refines A A := fun _ h => h
theorem Refines.trans {A B C : List Obs → Prop} (h₁ : Refines A B) (h₂ : Refines B C) :
    Refines A C := fun o h => h₂ o (h₁ o h)
theorem Equiv.refl (A : List Obs → Prop) : Equiv A A := ⟨Refines.refl A, Refines.refl A⟩
theorem Equiv.symm {A B : List Obs → Prop} (h : Equiv A B) : Equiv B A := ⟨h.2, h.1⟩
theorem Equiv.trans {A B C : List Obs → Prop} (h₁ : Equiv A B) (h₂ : Equiv B C) : Equiv A C :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- **The stack composes**: the ELF layer is equivalent to the WASI layer. -/
theorem Stack.equiv (K : Stack) : Equiv (K.obs .elf) (K.obs .wasi) :=
  ((((K.edge 0 (by decide)).trans (K.edge 1 (by decide))).trans (K.edge 2 (by decide))).trans
    (K.edge 3 (by decide))).trans (K.edge 4 (by decide))

/-- A stack whose ends are a process and a WASI program proves `ElfWasiEquiv`. -/
theorem ElfWasiEquiv.of_stack {P : List Obs → Prop} {W : P1Sem} {S : Subset} (K : Stack)
    (hP : K.obs .elf = P) (hW : K.obs .wasi = W.obs S) : ElfWasiEquiv P W S := by
  rw [ElfWasiEquiv, ← hP, ← hW]; exact K.equiv

/-! ## Safety bounds traces -/

variable {step : MState → Option MState} {E : SysEnv}

/-- **Every run is bounded by a safety proof** (at a `syscall` the user step is stuck, and no
early exit `Q`). -/
theorem procRun_of_ioSafe (hstuck : ∀ m, AtSyscall m → step m = none)
    {m : MState} {e : E.Model} {tr : List Event} (hr : ProcRun step E m e tr) :
    ∀ {A : List Event → Prop}, (∀ n, IoSafeN step E (fun _ _ _ => False) n m e A) → A tr := by
  induction hr with
  | stop m e => intro A h; exact (h 1).1
  | @step m m' e tr hs _ ih =>
    show ∀ {A : List Event → Prop}, (∀ n, IoSafeN step E (fun _ _ _ => False) n m e A) → A tr
    intro A h
    refine ih fun n => ?_
    rcases (h (n + 1)).2 with hq | ⟨m'', hs', hn⟩ | ⟨hat, -⟩
    · exact hq.elim
    · have hm : m'' = m' := Option.some.inj (hs'.symm.trans hs)
      exact hm ▸ hn
    · have hnone : step m = none := hstuck _ hat
      exact (Option.some_ne_none _ (hs.symm.trans hnone)).elim
  | @resume m m' e e' ch evs tr hat harm _ ih =>
    intro A h
    refine ih (A := fun tr => A (evs ++ tr)) fun n => ?_
    rcases (h (n + 1)).2 with hq | ⟨m'', hs', -⟩ | ⟨-, hall⟩
    · exact hq.elim
    · have hnone : step m = none := hstuck _ hat
      exact (Option.some_ne_none _ (hs'.symm.trans hnone)).elim
    · exact (hall ch).2 _ harm
  | @halt m e ch evs hat harm =>
    intro A h
    rcases (h 1).2 with hq | ⟨m'', hs', -⟩ | ⟨-, hall⟩
    · exact hq.elim
    · have hnone : step m = none := hstuck _ hat
      exact (Option.some_ne_none _ (hs'.symm.trans hnone)).elim
    · exact (hall ch).2 _ harm

/-- **The proved x86 `hello` runtimes refine the preview1 `hello`**: every trace of a run is a
prefix of the OS image of `fd_write(1, "hi"); proc_exit(0)`. -/
theorem helloLoop_procRun {c : MState → Option MState} {segs : List Silmaril.Process.LPS.Segment}
    {ch : Word} {e : Silmaril.Process.LPS.Model} (R : Silmaril.Wasi.Runtime.HelloLoop c segs ch e)
    (hstuck : ∀ m, AtSyscall m → c m = none) {tr : List Event}
    (hr : ProcRun c (lpsEnv segs) R.start e tr) :
    tr <+: Silmaril.Wasi.Versions.P1.osTrace ch Silmaril.Wasi.Versions.P1.helloP1 ++ [.exitEv 0 e.fs] :=
  procRun_of_ioSafe hstuck hr (Silmaril.Wasi.Versions.P1.helloLoop_p1 R)

theorem obsTrace_prefix {a b : List Event} (h : a <+: b) : obsTrace a <+: obsTrace b := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨obsTrace c, by simp [obsTrace]⟩

/-- The image of the preview1 `hello` on channel 1 is its observable image. -/
theorem hello_obs (fs : Silmaril.Process.LPS.Fs.FileSystem) :
    obsTrace (Silmaril.Wasi.Versions.P1.osTrace 1 Silmaril.Wasi.Versions.P1.helloP1 ++ [.exitEv 0 fs]) =
      Silmaril.Wasi.Versions.P1.helloP1.flatMap p1Obs := by
  rw [Silmaril.Wasi.Versions.P1.helloP1_os]
  simp [obsTrace, obsOfEvent, Silmaril.Wasi.Os.hiOut, Silmaril.Wasi.Examples.hiBytes,
    Silmaril.Wasi.Versions.P1.helloP1, p1Obs, ofP1, okAns, Silmaril.Wasi.okV, sysObs, bytesOf_bytesV]

theorem helloP1_in : InP1 S1 Silmaril.Wasi.Versions.P1.helloP1 := by
  intro e he s hs
  simp [Silmaril.Wasi.Versions.P1.helloP1] at he
  rcases he with rfl | rfl <;> simp [ofP1, okAns, Silmaril.Wasi.okV] at hs <;> subst hs <;> simp [SysEv.In, SysEv.name, S1]

/-- **One half of `Task.helloEquiv`**: every observable trace of a proved x86 `hello` runtime
is an observable trace of the preview1 `hello`. -/
theorem helloLoop_refines {c : MState → Option MState} {segs : List Silmaril.Process.LPS.Segment}
    {e : Silmaril.Process.LPS.Model} (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e)
    (hstuck : ∀ m, AtSyscall m → c m = none) :
    Refines (procObs c (lpsEnv segs) R.start e) (helloP1Sem.obs S1) := by
  rintro o ⟨tr, hr, rfl⟩
  refine ⟨_, List.prefix_refl _, helloP1_in, ?_⟩
  rw [← hello_obs e.fs]
  exact obsTrace_prefix (helloLoop_procRun R hstuck hr)

end Silmaril.Sim.WasiBridge

/-- info: 'Silmaril.Sim.WasiBridge.helloLoop_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.WasiBridge.helloLoop_refines

/-- info: 'Silmaril.Sim.WasiBridge.p1Obs_toP1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.WasiBridge.p1Obs_toP1
