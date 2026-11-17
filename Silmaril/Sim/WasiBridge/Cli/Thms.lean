module

public import Silmaril.Sim.WasiBridge.Cli.Defs
public import Silmaril.Sim.WasiBridge.Thms
public import Silmaril.Cli.Institution.Thms
public import Mathlib.Tactic.IntervalCases

/-!
# ELF ≡ WASI transfers CLI satisfaction

PROVED (standard axioms):

* `traceModel_mono`, `traceModel_eq`: trace refinement is model refinement, trace equivalence
  model equality;
* **`sat_iff_of_elfWasiEquiv`**: when a process is `ElfWasiEquiv` to a WASI program for every
  stdin, the two `L1` models satisfy the same sentences;
* `stack_sat_iff`: any two layers of a family of stacks satisfy the same sentences (ELF, ELF in
  the simulator, …, WASI);
* **`native_sat_of_wasi`**: a full model (e.g. `x86Model` of a glibc or musl binary) whose `L1`
  reduct runs are among a process's traces satisfies the lift of every `L1` sentence the
  equivalent WASI program satisfies (the inclusion is a hypothesis: `Task.nativeInTraces`);
* hello: `helloP1_prints` (the preview1 `hello` prints `hi` and exits `0`, at `L1`) and
  `helloLoop_prints` (**every proved x86 `hello` runtime prints `hi`**, through
  `helloLoop_refines`).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge

open Silmaril.Cli (Bytes)
open Silmaril.Cli.Institution (Level Model Sen Out1)

theorem traceModel_mono {P Q : Bytes → List Obs → Prop} (h : ∀ s, Refines (P s) (Q s)) :
    traceModel P ≤ traceModel Q := by
  rintro s o ⟨t, ht, he⟩
  exact ⟨t, h s t ht, he⟩

theorem traceModel_eq {P Q : Bytes → List Obs → Prop} (h : ∀ s, Equiv (P s) (Q s)) :
    traceModel P = traceModel Q :=
  le_antisymm (traceModel_mono fun s => (h s).1) (traceModel_mono fun s => (h s).2)

/-- **`ElfWasiEquiv` transfers CLI satisfaction, both ways.** -/
theorem sat_iff_of_elfWasiEquiv {P : Bytes → List Obs → Prop} {W : Bytes → P1Sem} {S : Subset}
    (h : ∀ s, ElfWasiEquiv (P s) (W s) S) (φ : Sen Level.stream.sig) :
    (traceModel P).Sat φ ↔ (p1Model W S).Sat φ := by
  rw [p1Model, traceModel_eq h]

/-- Any two layers of a family of stacks satisfy the same sentences. -/
theorem stack_sat_iff (K : Bytes → Stack) (φ : Sen Level.stream.sig) :
    (stackModel K .elf).Sat φ ↔ (stackModel K .wasi).Sat φ := by
  rw [stackModel, stackModel, traceModel_eq fun s => (K s).equiv]

/-- **Task (native runs among the traces)**: the `L1` runs of a full CLI model `M` (e.g. the
`x86Model` of a dynamically linked binary on glibc, or of a static musl binary) are among the
ended traces of the process semantics `P`. For one binary this is the agreement of the two
process models (the Program API's, and the LPS launch the simulator stack starts from) on its
observable runs. -/
def Task.nativeInTraces (M : Model Level.full.sig) (P : Bytes → List Obs → Prop) : Prop :=
  Level.stream.reduct M ≤ traceModel P

/-- **From WASI to a native binary**: given `ElfWasiEquiv` of the process to a WASI program and
the native runs among the process's traces, every `L1` sentence the WASI program satisfies
holds of the native binary (lifted to the full level). -/
theorem native_sat_of_wasi {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    {W : Bytes → P1Sem} {S : Subset} {φ : Sen Level.stream.sig}
    (hW : (p1Model W S).Sat φ) (hE : ∀ s, ElfWasiEquiv (P s) (W s) S)
    (hT : Task.nativeInTraces M P) : M.Sat (Level.lift φ) :=
  (Level.sat_lift_iff M φ).mpr (((sat_iff_of_elfWasiEquiv hE φ).mpr hW).anti hT)

/-! ## Hello -/

/-- The observable image of the preview1 `hello`. -/
def helloObs : List Obs := [.wr 1 0x68, .wr 1 0x69, .exit 0]

theorem helloP1_flat : Silmaril.Wasi.Versions.P1.helloP1.flatMap p1Obs = helloObs := by
  simp [Silmaril.Wasi.Versions.P1.helloP1, p1Obs, ofP1, Silmaril.Wasi.Versions.P1.okAns, Silmaril.Wasi.okV, sysObs,
    bytesOf_bytesV, Silmaril.Wasi.Examples.hiBytes, helloObs]

theorem flatMap_prefix {a b : List Silmaril.Wasi.WEv} (h : a <+: b) :
    a.flatMap p1Obs <+: b.flatMap p1Obs := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.flatMap p1Obs, by simp⟩

/-- An ended prefix of `helloObs` is all of it. -/
theorem helloObs_ended {t : List Obs} (h : t <+: helloObs) (he : (endCode t).isSome) :
    t = helloObs := by
  rw [List.prefix_iff_eq_take] at h
  have hl : t.length ≤ 3 := h.symm ▸ by simp [helloObs]
  generalize hn : t.length = n at h hl
  subst h
  interval_cases n <;> simp_all [endCode, helloObs]

/-- **The preview1 `hello` prints `hi` and exits `0`** (level `L1`, every stdin). -/
theorem helloP1_prints :
    (p1Model (fun _ => helloP1Sem) S1).Sat (Sen.prints (cliBytes [0x68, 0x69])) := by
  rintro s o ⟨t', ⟨t, ht, -, hp⟩, he⟩
  have hp' : t' <+: helloObs := helloP1_flat ▸ hp.trans (flatMap_prefix ht)
  have hs : (endCode t').isSome := by
    cases h : endCode t' <;> simp_all [out1]
  have : t' = helloObs := helloObs_ended hp' hs
  subst this
  simp [out1, endCode, helloObs, writtenOn] at he
  subst he
  exact ⟨rfl, rfl⟩

/-- **Every proved x86 `hello` runtime prints `hi` and exits `0`** (level `L1`), through its
refinement of the preview1 `hello`. -/
theorem helloLoop_prints {c : Silmaril.X86.MState → Option Silmaril.X86.MState}
    {segs : List Silmaril.Process.LPS.Segment} {e : Silmaril.Process.LPS.Model}
    (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e)
    (hstuck : ∀ m, Silmaril.Machine.Process.LpsBridge.AtSyscall m → c m = none) :
    (traceModel fun _ => procObs c (Silmaril.Machine.Process.IoSpec.lpsEnv segs) R.start e).Sat
      (Sen.prints (cliBytes [0x68, 0x69])) :=
  helloP1_prints.anti (traceModel_mono fun _ => helloLoop_refines R hstuck)

end Silmaril.Sim.WasiBridge
