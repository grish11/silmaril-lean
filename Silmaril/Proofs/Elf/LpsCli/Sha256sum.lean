module

public import Silmaril.Elf.LpsCli.Sha256sum.Defs
public import Silmaril.Elf.LpsCli.Thms
public import Silmaril.Cli.Institution.Std.Thms
public import Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Thms
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Close
public import Silmaril.Process.LPS.Problems.Sha256Cli.Registry

@[expose] public section

/-! Proofs for `Silmaril.Elf.LpsCli.Sha256sum` (the header `Silmaril.Elf.LpsCli.Sha256sum.Thms` restates them). -/

namespace Silmaril.Proofs.Elf.LpsCli.Sha256sum

open Silmaril.Elf.LpsCli Silmaril.Elf.LpsCli.Sha256sum
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Problems
open Silmaril.Cli.Institution (Level Model Sen Out1)

theorem staticModel_sat : staticModel.Sat Silmaril.Cli.Institution.Std.sha256Stdin := by
  refine sat_filter_of_prefix fun s oracle refusals limit en inp records tr hl ht => ?_
  obtain ⟨hp, hs, ha, hv, he⟩ := hl
  rw [GnuSha256sum.parsed, Option.some.injEq] at hp
  subst hp
  have hP := GnuSha256sum.Close.lpsPartial_close oracle refusals limit en inp (lpsBytes s)
    ⟨hs, ha, hv, he⟩
  have hpre := hP.safe tr ht
  have e : GnuSha256sum.idealTrace (lpsBytes s) inp.fs =
      filterTrace (lpsBytes s) (lpsBytes (Silmaril.Apps.Sha256sum.Sys.stdinRecord s)) inp.fs := by
    have hs' : GnuSha256sum.toSpec (lpsBytes s) = s := cliBytes_lpsBytes s
    rw [GnuSha256sum.idealTrace, GnuSha256sum.expected_eq_record, hs']
    rfl
  rwa [e] at hpre

theorem static_agrees_glibc {s : Silmaril.Cli.Bytes} {o o' : Out1} (h : staticModel.Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree staticModel_sat
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std h h'

theorem filterModel_sat : filterModel.Sat (Sen.filter hexLine) := by
  refine sat_filter_of_prefix fun s oracle refusals limit en inp records tr hl ht => ?_
  obtain ⟨hp, hs, -, hv, he⟩ := hl
  rw [Sha256Cli.parsed, Option.some.injEq] at hp
  subst hp
  have hP := Sha256Cli.Registry.lpsPartial_solution oracle refusals limit en inp (lpsBytes s)
    ⟨hs, hv, he⟩
  have hpre := hP.safe tr ht
  simpa [hexLine, Sha256Cli.idealTrace, filterTrace] using hpre

theorem sha256Stdin_eq_hexLine (s : Silmaril.Cli.Bytes) :
    Silmaril.Apps.Sha256sum.Sys.stdinRecord s =
      (hexLine s).dropLast ++ Silmaril.Apps.Sha256sum.lit "  -\n" := by
  have h := Sha256Cli.gnu_stdout (lpsBytes s)
  have h2 := congrArg cliBytes h
  simp only [cliBytes, List.map_map, List.map_append, List.map_dropLast] at h2
  simpa [hexLine, cliBytes, lpsBytes, Function.comp_def, Silmaril.Apps.Sha256sum.lit] using h2

end Silmaril.Proofs.Elf.LpsCli.Sha256sum
