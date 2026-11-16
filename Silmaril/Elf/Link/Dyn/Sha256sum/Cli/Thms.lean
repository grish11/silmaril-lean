module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Defs
public import Silmaril.Elf.Link.Dyn.Program.Cli.Thms
public import Silmaril.Cli.Institution.Std.Defs

/-!
# GNU `sha256sum` on glibc satisfies the stdin digest filter

PROVED (standard axioms):

* **`stdinModel_sat`**: the `L1` model of the pinned GNU `sha256sum` on glibc satisfies
  `Sen.filter stdinRecord` (stdout `hex(SHA-256(d)) ++ "  -\n"`, exit `0`, for every stdin `d`),
  from `Sha256sum.sha256sum_stdin` and silmaril's `Sys.sha256sum_stdin`; `stdinModel_std`: the
  same as the standard sentence `Std.sha256Stdin`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Cli.Institution (Level Model Sen Out1)

/-- The digest line of the stdin tier: `hex(SHA-256(d))`, two spaces, `-`, newline. -/
abbrev stdinRecord : Silmaril.Cli.Bytes → Silmaril.Cli.Bytes := Silmaril.Apps.Sha256sum.Sys.stdinRecord

private theorem toSpec_ofSpec' (d : List UInt8) : toSpec (ofSpec d) = d := by
  simp [toSpec, ofSpec, Function.comp_def]

/-- **GNU `sha256sum` on glibc prints the digest line of its stdin and exits `0`.** -/
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

/-- GNU `sha256sum` on glibc meets the standard `L1` sentence `Std.sha256Stdin`. -/
theorem stdinModel_std : stdinModel.Sat Silmaril.Cli.Institution.Std.sha256Stdin := stdinModel_sat

end Silmaril.Elf.Link.Dyn.Sha256sum
