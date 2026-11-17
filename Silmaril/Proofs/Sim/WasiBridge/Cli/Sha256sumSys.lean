module

public import Silmaril.Sim.WasiBridge.Cli.Sha256sumSys.Defs
public import Silmaril.Sim.WasiBridge.Sys.Thms
public import Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms

@[expose] public section

/-! Proofs for `Silmaril.Sim.WasiBridge.Sha256sumSys` (the header `Silmaril.Sim.WasiBridge.Cli.Sha256sumSys.Thms` restates them). -/

namespace Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys

open Silmaril.Sim.WasiBridge Silmaril.Sim.WasiBridge.Sha256sumSys
open Silmaril.Sim.WasiBridge.Sys
open Silmaril.Apps.Sha256sum (Bytes World lit sha256sum)
open Silmaril.Apps.Sha256sum.Sys (refMachine refStep RefState WorldStep StdinDom Exec
  stdinRecord)
open Silmaril.Cli.Institution (Level Model Out1)
open Silmaril.Cli.Institution.Std (sha256Stdin)

theorem stdinWorld_dom (s : Bytes) : StdinDom (stdinWorld s) := ⟨rfl, ⟨s, rfl⟩, rfl⟩

theorem sha256sum_stdinWorld (s : Bytes) :
    sha256sum (stdinWorld s) = { stdout := stdinRecord s, stderr := [], status := 0 } :=
  Silmaril.Apps.Sha256sum.Sys.sha256sum_stdin (lit "sha256sum") false _ s

theorem ref_satisfiesRel :
    Silmaril.Apps.Sha256sum.Sys.SatisfiesRel refMachine WorldStep refInit StdinDom := by
  intro w hw st hst evs n hx
  subst hst
  exact Silmaril.Apps.Sha256sum.Sys.ref_satisfies w hw evs n hx

theorem refObs_sat : (traceModel refObs).Sat sha256Stdin := by
  intro s o ho
  obtain ⟨h1, h2⟩ := machModel_sat ref_satisfiesRel stdinWorld_dom s o ho
  rw [sha256sum_stdinWorld] at h1 h2
  exact ⟨h1, h2⟩

theorem wasiSha256_ref : Task.wasiSha256 refP1 S1 :=
  refObs_sat.anti (traceModel_mono fun s => machP1_refines S1 s)

theorem not_exec_failed {E : Silmaril.Apps.Sha256sum.Sys.Env} {k : Silmaril.Apps.Sha256sum.Sys.KState}
    {evs : List SEvent} {n : Nat} : ¬ Exec refMachine E .failed k evs n := by
  intro h
  rcases h with ⟨hs⟩ | ⟨hs, _⟩ | ⟨hs, _, _⟩ <;> simp [refMachine, refStep] at hs

theorem ref_repr {w : World} {st : refMachine.State} {k : Silmaril.Apps.Sha256sum.Sys.KState}
    {evs : List SEvent} {n : Nat} (h : Exec refMachine (WorldStep w) st k evs n)
    (hi : RInv st) : ∀ e ∈ evs, SEvent.Repr e := by
  induction h with
  | exit => simp
  | @tau s s' k evs n hs _ ih =>
    apply ih
    cases s with
    | writing p =>
      cases p with
      | nil =>
        simp only [refMachine, refStep] at hs
        cases hs; trivial
      | cons x xs => simp [refMachine, refStep] at hs
    | closing m =>
      simp only [refMachine, refStep] at hs
      split at hs <;> simp at hs
    | _ => simp [refMachine, refStep] at hs
  | @call s c f k r k' evs n hs he hx ih =>
    cases s with
    | reading acc =>
      simp only [refMachine, refStep] at hs
      cases hs
      cases r with
      | data b =>
        intro e he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact ⟨by decide, by decide⟩
        · refine ih ?_ e he'
          cases b with
          | nil => exact (Silmaril.Apps.Sha256sum.Sys.stdinRecord_length acc).le
          | cons _ _ => trivial
      | ok _ => exact (not_exec_failed hx).elim
      | err _ => exact (not_exec_failed hx).elim
    | writing p =>
      cases p with
      | nil => simp [refMachine, refStep] at hs
      | cons x xs =>
        simp only [refMachine, refStep] at hs
        cases hs
        cases r with
        | ok m =>
          have hm : m ≤ (x :: xs).length := by
            cases he with
            | writeOut _ _ ha => exact ha.1
            | writeErr _ ha => exact ha.1
          have hl : (x :: xs).length ≤ 68 := hi
          intro e he'
          rcases List.mem_cons.1 he' with rfl | he'
          · exact ⟨by decide, by omega⟩
          · refine ih ?_ e he'
            show ((x :: xs).drop m).length ≤ 68
            simp only [List.length_drop]
            omega
        | data _ => exact (not_exec_failed hx).elim
        | err _ => exact (not_exec_failed hx).elim
    | closing m =>
      simp only [refMachine, refStep] at hs
      split at hs
      · cases hs
        cases r with
        | ok _ =>
          intro e he'
          rcases List.mem_cons.1 he' with rfl | he'
          · show m < 2 ^ 32
            omega
          · exact ih trivial e he'
        | data _ => exact (not_exec_failed hx).elim
        | err _ => exact (not_exec_failed hx).elim
      · simp at hs
    | failed => simp [refMachine, refStep] at hs

theorem ref_allRepr : AllRepr refMachine WorldStep refInit stdinWorld := by
  intro s st evs n hi hx
  subst hi
  exact ref_repr hx trivial

theorem ref_equiv (s : Bytes) : ElfWasiEquiv (refObs s) (refP1 s) S1 :=
  machP1_equiv ref_allRepr s

theorem wasiSha256sum_sat {W : Bytes → P1Sem} (h : Task.wasiRefinesRef W) :
    Task.wasiSha256 W S1 :=
  wasiSha256_ref.anti (traceModel_mono h)

theorem sim_sat_of_refines {P : Bytes → List Obs → Prop}
    (h : ∀ s, Refines (P s) ((refP1 s).obs S1)) : (traceModel P).Sat sha256Stdin :=
  wasiSha256_ref.anti (traceModel_mono h)

theorem simSha256sum_sat {P : Bytes → List Obs → Prop} (h : Task.simSha256sumEquiv P) :
    (traceModel P).Sat sha256Stdin :=
  sim_sat_of_refines fun s => (h s).1

theorem simSha256sum_equiv_of_stack {P : Bytes → List Obs → Prop} (h : Task.sha256Stack P) :
    Task.simSha256sumEquiv P := fun s =>
  let ⟨K, hP, hW⟩ := h s
  ElfWasiEquiv.of_stack K hP hW

theorem Stack.equiv_wasi (K : Stack) : ∀ l, Equiv (K.obs l) (K.obs .wasi)
  | .elf => K.equiv
  | .bytesSim => (((K.edge 1 (by decide)).trans (K.edge 2 (by decide))).trans
      (K.edge 3 (by decide))).trans (K.edge 4 (by decide))
  | .pcalls => ((K.edge 2 (by decide)).trans (K.edge 3 (by decide))).trans (K.edge 4 (by decide))
  | .lform => (K.edge 3 (by decide)).trans (K.edge 4 (by decide))
  | .adapted => K.edge 4 (by decide)
  | .wasi => Silmaril.Sim.WasiBridge.Equiv.refl _

/-- **Every layer of a sha256sum stack meets the standard sentence**: the ELF, the ELF run in
the WASM simulator (`.bytesSim`), the P-calls and L forms, the adapted module. -/
theorem stack_sat (K : Bytes → Stack) (hW : ∀ s, (K s).obs .wasi = (refP1 s).obs S1)
    (l : Layer) : (stackModel K l).Sat sha256Stdin :=
  sim_sat_of_refines (P := fun s => (K s).obs l) fun s => by
    rw [← hW s]
    exact (Stack.equiv_wasi (K s) l).1

theorem native_sat_of_refines {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    (h : ∀ s, Refines (P s) ((refP1 s).obs S1)) (hT : Task.nativeInTraces M P) :
    M.Sat (Level.lift sha256Stdin) :=
  (Level.sat_lift_iff M sha256Stdin).mpr ((sim_sat_of_refines h).anti hT)

theorem native_sat_of_sim {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    (hE : Task.simSha256sumEquiv P) (hT : Task.nativeInTraces M P) :
    M.Sat (Level.lift sha256Stdin) :=
  native_sat_of_refines (fun s => (hE s).1) hT

theorem native_reduct_sat_of_sim {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    (hE : Task.simSha256sumEquiv P) (hT : Task.nativeInTraces M P) :
    (Level.stream.reduct M).Sat sha256Stdin :=
  (simSha256sum_sat hE).anti hT

theorem sim_agrees_glibc {P : Bytes → List Obs → Prop} (hE : Task.simSha256sumEquiv P)
    {s : Bytes} {o o' : Out1} (h : (traceModel P).Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  sha256_agrees_glibc wasiSha256_ref hE h h'

theorem min_refines_ref (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) (s : Bytes) :
    Refines (minObs r11Of s) (refObs s) :=
  machObs_mono (h r11Of) stdinWorld_dom s

theorem min_sat (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) :
    (traceModel (minObs r11Of)).Sat sha256Stdin :=
  refObs_sat.anti (traceModel_mono (min_refines_ref h r11Of))

theorem min_refines_wasi (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) (s : Bytes) :
    Refines (minObs r11Of s) ((refP1 s).obs S1) :=
  (min_refines_ref h r11Of s).trans (ref_equiv s).1

theorem min_equiv (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) (hc : Task.minComplete r11Of) :
    Task.simSha256sumEquiv (minObs r11Of) := fun s =>
  ⟨min_refines_wasi h r11Of s, hc s⟩

theorem min_agrees_glibc (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) {s : Bytes} {o o' : Out1}
    (hr : (traceModel (minObs r11Of)).Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree (min_sat h r11Of)
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std hr h'

end Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys
