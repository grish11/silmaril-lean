module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Defs
public import Silmaril.Elf.Link.Dyn.Program.Cli.Thms
public import Silmaril.Cli.Institution.Std.Defs

@[expose] public section

/-! Proofs for `Silmaril.Elf.Link.Dyn.Sha256sum` (the header `Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Thms` restates them). -/

namespace Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.Cli

open Silmaril.Elf.Link.Dyn Silmaril.Elf.Link.Dyn.Sha256sum
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Cli.Institution (Level Model Sen Out1)

private theorem toSpec_ofSpec' (d : List UInt8) : toSpec (ofSpec d) = d := by
  simp [toSpec, ofSpec, Function.comp_def]

theorem stdinModel_sat : stdinModel.Sat (Sen.filter stdinRecord) := by
  rintro d o ⟨Fk, Fc, Fl, b, kb, lb, ldb, res, sr, sc, ifn, lazy, E, R, W, s, argc, a0, u, e, out,
    hk, hc, hl, hsr, hsc, I, T, XO, hload, hs, hR, hA, hp, hu, rfl⟩
  have hm := sha256sum_stdin hk hc hl hsr hsc I T XO hload hs hR hA false (fun _ => .ok [])
  have hspec : Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 (ofSpec d) false fun _ => .ok []) =
      { stdout := stdinRecord d, stderr := [], status := 0 } := by
    rw [stdinWorld, toSpec_ofSpec']
    exact Silmaril.Apps.Sha256sum.Sys.sha256sum_stdin _ _ _ _
  rw [hspec] at hm
  obtain ⟨w, hw, hw', -⟩ := Program.must_reach hm hp (Program.step_stop_of_done hu)
    (fun x ⟨_, hx, _⟩ t => Program.not_okStep_of_done hx)
  rw [hu] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  subst hw'
  exact ⟨by simp [toSpec, Function.comp_def], rfl⟩

theorem stdinModel_std : stdinModel.Sat Silmaril.Cli.Institution.Std.sha256Stdin := stdinModel_sat

end Silmaril.Proofs.Elf.Link.Dyn.Sha256sum.Cli
