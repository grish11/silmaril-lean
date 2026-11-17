module

public import Silmaril.Sim.WasiBridge.Sys.Defs
public import Silmaril.Sim.WasiBridge.Cli.Thms

/-!
# System-call machines through the ELF ≡ WASI bridge

PROVED (standard axioms):

* `p1Obs_sevP1`, `p1Obs_runP1`: the adapter preserves observables, event by event and on whole
  exiting runs; `inP1_runP1`: the image stays within `S1` (`fd_close` has no syscall image, so
  it is outside `ofP1`'s domain and does not count);
* **`machP1_refines`**: the WASI reading of a machine refines its observable traces, for every
  subset; **`machP1_equiv`**: when every exiting run is represented by the adapter
  (`AllRepr`), the two readings are `ElfWasiEquiv` within `S1`;
* **`machObs_mono`**: silmaril's call-for-call trace refinement of machines (`TraceRefinesRel`)
  is refinement of observable traces;
* **`machModel_sat`**: a machine that `SatisfiesRel` the `sha256sum` specification on the worlds
  `w s` is an `L1` CLI model of it (stdout and exit status of `sha256sum (w s)`).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Sys

open Silmaril.Wasi (WEv)
open Silmaril.Wasi.Versions.P1 (fn okAns)
open Silmaril.Apps.Sha256sum (Bytes World sha256sum)
open Silmaril.Apps.Sha256sum.Sys (Machine Env Call Ret KState Exec)
open Silmaril.Cli.Institution (Level Model Sen Out1)

theorem bits_take (b : Bytes) (k : Nat) : bits (b.take k) = (bits b).take k := by
  simp [bits, List.map_take]

theorem cliBytes_bits (b : Bytes) : cliBytes (bits b) = b := by
  simp [cliBytes, bits, Function.comp_def]

/-- Exit statuses are reduced modulo 256. -/
theorem exec_lt {M : Machine} {E : Env} {s : M.State} {k : KState} {evs : List SEvent} {n : Nat}
    (h : Exec M E s k evs n) : n < 256 := by
  induction h with
  | exit => exact Nat.mod_lt _ (by decide)
  | tau _ _ ih => exact ih
  | call _ _ _ ih => exact ih

/-! ## The adapter preserves observables -/

theorem p1Obs_sevP1 (e : SEvent) (h : SEvent.Repr e) : (sevP1 e).flatMap p1Obs = sevObs e := by
  rcases e with ⟨_ | ⟨fd, n⟩ | ⟨fd, b⟩ | fd, k | b | er⟩ <;> simp only [SEvent.Repr] at h
  · exact p1Obs_toP1 (.read fd n (bits b)) h
  · simp only [sevP1, sevObs]
    rw [p1Obs_toP1 (.write fd (bits b) k) h, bits_take]
    rfl
  · rfl

theorem p1Obs_exit {n : Nat} (hn : n < 256) : (toP1 (.exit n)).flatMap p1Obs = [.exit n] := by
  rw [p1Obs_toP1 (.exit n) hn]
  simp [sysObs, Nat.mod_eq_of_lt hn]

theorem p1Obs_runP1 {evs : List SEvent} {n : Nat} (hR : ∀ e ∈ evs, SEvent.Repr e) (hn : n < 256) :
    (runP1 evs n).flatMap p1Obs = runObs evs n := by
  induction evs with
  | nil => simpa [runP1, runObs] using p1Obs_exit hn
  | cons e evs ih =>
    have h1 := p1Obs_sevP1 e (hR e (by simp))
    have h2 := ih fun e' he' => hR e' (by simp [he'])
    simp only [runP1, runObs, List.flatMap_cons, List.flatMap_append, List.append_assoc] at h2 ⊢
    rw [h1, h2]

theorem inP1_toP1 {S : Subset} (e : SysEv) (hb : e.Bounded) (hS : e.name ∈ S) :
    InP1 S (toP1 e) := by
  intro x hx y hy
  have : y ∈ (toP1 e).flatMap ofP1 := List.mem_flatMap.2 ⟨x, hx, hy⟩
  rw [ofP1_toP1 e hb] at this
  rw [List.mem_singleton.1 this]
  exact hS

theorem inP1_sevP1 (e : SEvent) (h : SEvent.Repr e) : InP1 S1 (sevP1 e) := by
  rcases e with ⟨_ | ⟨fd, n⟩ | ⟨fd, b⟩ | fd, k | b | er⟩ <;> simp only [SEvent.Repr] at h
  · exact inP1_toP1 (.read fd n (bits b)) h (by simp [SysEv.name, S1])
  · exact inP1_toP1 (.write fd (bits b) k) h (by simp [SysEv.name, S1])
  · intro x hx y hy
    simp only [sevP1, List.mem_singleton] at hx
    subst hx
    exact absurd hy (by simp [ofP1, okAns, Silmaril.Wasi.okV])

theorem InP1.append {S : Subset} {a b : List WEv} (ha : InP1 S a) (hb : InP1 S b) :
    InP1 S (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem inP1_runP1 {evs : List SEvent} {n : Nat} (hR : ∀ e ∈ evs, SEvent.Repr e) (hn : n < 256) :
    InP1 S1 (runP1 evs n) := by
  refine InP1.append ?_ (inP1_toP1 (.exit n) hn (by simp [SysEv.name, S1]))
  intro x hx
  obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hx
  exact inP1_sevP1 e (hR e he) x hx

/-! ## The two readings of a machine -/

variable {M : Machine} {env : World → Env} {init : World → M.State → Prop} {w : Bytes → World}

/-- **The WASI reading refines the observable traces**, for every subset. -/
theorem machP1_refines (S : Subset) (s : Bytes) :
    Refines ((machP1 M env init w s).obs S) (machObs M env init w s) := by
  rintro o ⟨t, ⟨st, evs, n, hi, hx, hR, ht⟩, -, ho⟩
  refine ⟨st, evs, n, hi, hx, ?_⟩
  rw [← p1Obs_runP1 hR (exec_lt hx)]
  exact ho.trans (flatMap_prefix ht)

/-- The observable traces refine the WASI reading, when the adapter represents every run. -/
theorem machObs_refines (hA : AllRepr M env init w) (s : Bytes) :
    Refines (machObs M env init w s) ((machP1 M env init w s).obs S1) := by
  rintro o ⟨st, evs, n, hi, hx, ho⟩
  have hR := hA s st evs n hi hx
  refine ⟨runP1 evs n, ⟨st, evs, n, hi, hx, hR, List.prefix_refl _⟩,
    inP1_runP1 hR (exec_lt hx), ?_⟩
  rw [p1Obs_runP1 hR (exec_lt hx)]
  exact ho

/-- **A machine is `ElfWasiEquiv` to its WASI reading** (within `S1`), when the adapter
represents every exiting run. -/
theorem machP1_equiv (hA : AllRepr M env init w) (s : Bytes) :
    ElfWasiEquiv (machObs M env init w s) (machP1 M env init w s) S1 :=
  ⟨machObs_refines hA s, machP1_refines S1 s⟩

/-- **Trace refinement of machines is refinement of observable traces.** -/
theorem machObs_mono {B A : Machine} {initB : World → B.State → Prop} {initA : World → A.State}
    {dom : World → Prop}
    (h : Silmaril.Apps.Sha256sum.Sys.TraceRefinesRel B A env initB initA dom)
    (hw : ∀ s, dom (w s)) (s : Bytes) :
    Refines (machObs B env initB w s) (machObs A env (fun w st => st = initA w) w s) := by
  rintro o ⟨st, evs, n, hi, hx, ho⟩
  exact ⟨initA (w s), evs, n, rfl, h (w s) (hw s) st hi evs n hx, ho⟩

/-! ## A machine as a CLI model -/

theorem writtenOn_append (fd : Nat) (a b : List Obs) :
    writtenOn fd (a ++ b) = writtenOn fd a ++ writtenOn fd b := by
  simp [writtenOn, List.filterMap_append]

theorem cliBytes_append (a b : List (BitVec 8)) : cliBytes (a ++ b) = cliBytes a ++ cliBytes b :=
  List.map_append

theorem writtenOn_sevObs (evs : List SEvent) :
    cliBytes (writtenOn 1 (evs.flatMap sevObs)) = Silmaril.Apps.Sha256sum.Sys.written 1 evs := by
  induction evs with
  | nil => rfl
  | cons e evs ih =>
    rw [List.flatMap_cons, writtenOn_append, cliBytes_append, ih]
    rcases e with ⟨_ | ⟨fd, n⟩ | ⟨fd, b⟩ | fd, k | b | er⟩ <;>
      simp [sevObs, writtenOn, Silmaril.Apps.Sha256sum.Sys.written, List.filterMap_map,
        cliBytes]
    by_cases hfd : fd = 1
    · subst hfd
      simp [bits, Function.comp_def]
    · simp [hfd]

theorem not_exit_sevObs (evs : List SEvent) (c : Nat) : Obs.exit c ∉ evs.flatMap sevObs := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro e _
  rcases e with ⟨_ | ⟨fd, n⟩ | ⟨fd, b⟩ | fd, k | b | er⟩ <;> simp [sevObs]

theorem endCode_eq_some {o : List Obs} {c : Nat} (h : endCode o = some c) :
    o.getLast? = some (.exit c) := by
  unfold endCode at h
  split at h <;> simp_all

/-- An ended prefix of an exiting run's observables is all of them. -/
theorem eq_of_prefix_ended {evs : List SEvent} {n : Nat} {o : List Obs}
    (h : o <+: runObs evs n) (he : (endCode o).isSome) : o = runObs evs n := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 he
  have hl := endCode_eq_some hc
  have hmem : Obs.exit c ∈ o := List.mem_of_getLast? hl
  rw [List.prefix_iff_eq_take] at h
  unfold runObs at h ⊢
  by_cases hk : o.length ≤ (evs.flatMap sevObs).length
  · rw [List.take_append_of_le_length hk] at h
    have : Obs.exit c ∈ evs.flatMap sevObs := (List.take_prefix _ _).subset (h ▸ hmem)
    exact absurd this (not_exit_sevObs evs c)
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at h
    exact h

theorem out1_runObs (evs : List SEvent) (n : Nat) :
    out1 (runObs evs n) =
      some { stdout := Silmaril.Apps.Sha256sum.Sys.written 1 evs, exit := UInt8.ofNat n } := by
  simp only [out1, endCode, runObs, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.map_some, writtenOn_append, Option.some.injEq]
  rw [cliBytes_append, writtenOn_sevObs]
  simp [writtenOn, cliBytes]

/-- **A machine that meets the `sha256sum` specification is a CLI model of it** (level `L1`):
on stdin `s`, stdout and exit status are those of `sha256sum (w s)`. -/
theorem machModel_sat {dom : World → Prop}
    (h : Silmaril.Apps.Sha256sum.Sys.SatisfiesRel M env init dom) (hw : ∀ s, dom (w s)) :
    (traceModel (machObs M env init w)).Sat fun s o =>
      o.stdout = (sha256sum (w s)).stdout ∧ o.exit = UInt8.ofNat (sha256sum (w s)).status := by
  rintro s o ⟨t, ⟨st, evs, n, hi, hx, ht⟩, he⟩
  have hs : (endCode t).isSome := by
    cases h' : endCode t <;> simp_all [out1]
  rw [eq_of_prefix_ended ht hs, out1_runObs, Option.some.injEq] at he
  subst he
  have := h (w s) (hw s) st hi evs n hx
  rw [← this]
  exact ⟨rfl, rfl⟩

end Silmaril.Sim.WasiBridge.Sys
