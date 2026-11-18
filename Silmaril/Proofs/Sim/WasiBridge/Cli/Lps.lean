module

public import Silmaril.Sim.WasiBridge.Cli.Lps.Defs
public import Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms
public import Silmaril.Elf.LpsCli.Sha256sum.Thms

@[expose] public section

/-! Proofs for `Silmaril.Sim.WasiBridge.Lps` (the header `Silmaril.Sim.WasiBridge.Cli.Lps.Thms` restates them). -/

namespace Silmaril.Proofs.Sim.WasiBridge.Cli.Lps

open Silmaril.Sim.WasiBridge Silmaril.Sim.WasiBridge.Lps
open Silmaril.Process.LPS (Event)
open Silmaril.Cli.Institution (Level Model Sen Out1)
open Silmaril.Elf.LpsCli

theorem obsTrace_eq (tr : List Event) : obsTrace tr = (tr.filter Visible).map obs1 := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    cases e <;> simp_all [obsTrace, obsOfEvent, Visible, obs1, List.filter_cons]

theorem writtenOn_obsTrace (tr : List Event) : writtenOn 1 (obsTrace tr) = stdoutOf tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    cases e <;> simp_all [obsTrace, obsOfEvent, writtenOn, stdoutOf, List.filterMap_cons]

theorem endCode_obsTrace (tr : List Event) :
    endCode (obsTrace tr) = (exitOf tr).map (·.toNat) := by
  rw [obsTrace_eq, endCode, exitOf, List.getLast?_map]
  rcases (tr.filter Visible).getLast? with _ | e
  · rfl
  · cases e <;> rfl

theorem out1_obsTrace (tr : List Event) : out1 (obsTrace tr) = out1Of tr := by
  simp only [out1, out1Of, endCode_obsTrace, writtenOn_obsTrace, Option.map_map]
  rfl

theorem lpsModel_eq (file : Silmaril.Formats.ELF.Bytes) (isa : Isa) :
    lpsModel file isa = traceModel (lpsTraces file isa) := by
  ext s o
  constructor
  · rintro ⟨tr, h, ho⟩
    exact ⟨obsTrace tr, ⟨tr, h, rfl⟩, by rw [out1_obsTrace]; exact ho⟩
  · rintro ⟨t, ⟨tr, h, rfl⟩, ho⟩
    exact ⟨tr, h, by rw [← out1_obsTrace]; exact ho⟩

theorem staticTraces_sat : (traceModel staticTraces).Sat Silmaril.Cli.Institution.Std.sha256Stdin := by
  rw [← lpsModel_eq]; exact Sha256sum.staticModel_sat

theorem wasiSha256_of_static {W : Silmaril.Cli.Bytes → P1Sem} {S : Subset}
    (hE : ∀ s, ElfWasiEquiv (staticTraces s) (W s) S) : Task.wasiSha256 W S :=
  (sat_iff_of_elfWasiEquiv hE _).mp staticTraces_sat

theorem wasi_agrees_glibc_of_static {W : Silmaril.Cli.Bytes → P1Sem} {S : Subset}
    (hE : ∀ s, ElfWasiEquiv (staticTraces s) (W s) S) {s : Silmaril.Cli.Bytes} {o o' : Out1}
    (h : (p1Model W S).Run s o) (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') :
    o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree (wasiSha256_of_static hE)
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std h h'

end Silmaril.Proofs.Sim.WasiBridge.Cli.Lps
