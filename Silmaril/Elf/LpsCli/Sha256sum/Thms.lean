module

public import Silmaril.Elf.LpsCli.Sha256sum.Defs
public import Silmaril.Elf.LpsCli.Thms
public import Silmaril.Cli.Institution.Std.Thms
public import Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Thms
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Close
public import Silmaril.Process.LPS.Problems.Sha256Cli.Registry

/-!
# The static sha256 executables satisfy their CLI sentences

PROVED (standard axioms, no hypothesis):

* **`staticModel_sat`**: `sha256sum-min` under LPS ⊨ `Std.sha256Stdin`: on every finite stdin `d`,
  every ended run writes `hex(SHA-256(d)) ++ "  -\n"` and exits `0`. From silmaril's release
  theorem `GnuSha256sum.Close.lpsPartial_close` by `sat_filter_of_prefix`.
* **`static_agrees_glibc`**: every run of `sha256sum-min` under LPS and every run of the real GNU
  `sha256sum` on glibc (`Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel`) on the same stdin give
  the same stdout and exit code (`Std.sha256Stdin_agree` with `stdinModel_std`).
* `filterModel_sat`: the `sha256` filter under LPS ⊨ `Sen.filter hexLine`
  (`Sha256Cli.lpsPartial_solution`).
* `sha256Stdin_eq_hexLine`: the two sentences' outputs differ only in the line end:
  `stdinRecord d = (hexLine d).dropLast ++ "  -\n"` (`Sha256Cli.gnu_stdout`).

## Two models of one sentence: what each trusts

Both rows are statements of the form `M ⊨ Std.sha256Stdin` at `L1`, partial correctness (runs
that fault, block or diverge have no observation). They differ in the model `M`:

| | `staticModel` (`sha256sum-min`, static) | `stdinModel` (GNU `sha256sum`, glibc) |
|---|---|---|
| executable | pinned 35512-byte ELF, libc-free; bytes as a Lean list (`GnuSha256sum.elfNat`), checked against the file by `scripts/sha256sum/gen_gnu_lps_elf.py --check` | pinned Ubuntu coreutils 9.4 `examples/elf/pinned/gnu-sha256sum`, read through generated chunk facts (`ChunksOf`) |
| loader | LPS `X86Launch` of the parsed `PT_LOAD` segments (`ELFImage.parse`, proved) | `ExeLoaded`: the ld.so relocation model with `libcrypto.so.3`, `libc.so.6`, `ld.so` (any bases, ifunc choice, binding mode) |
| libraries | none | glibc and libcrypto import contracts as hypotheses of each run (`MainImps`, `TailImps`, `ExitOk`, resource bounds `maxAllocs`, `maxHeap`) |
| process start | LPS launch: any valid input and entry, `argv` of one element | `ShaStartState` (a start state the kernel may produce) and `MainLib` (the library enters `main` with `argv = [a0]`) |
| instruction semantics | `X86.Ext8` with an oracle for flags undefined at `syscall` (every oracle) | the Program API's process machine (`Program.OkStep`) over the open x86 machine |
| kernel | LPS (port of rocq-linux-process-semantics): byte-granular `read`/`write`, arbitrary short transfers, refusal configurations quantified | the stream representation of stdin/stdout in the import contracts (`ShaRep`) |
| run hypotheses | none: `StdinLaunch` only fixes the stdin tier | the contracts above, per run (a run exists only in worlds that satisfy them) |
| proof | `Process.LPS.Problems.GnuSha256sum.Close` (VCs by segment, no hypothesis) | `Elf.Link.Dyn.Sha256sum.sha256sum_stdin` |

Neither model is derived from the other. `static_agrees_glibc` relates the two programs through
the sentence alone. Relating the models themselves (e.g. LPS as a refinement of the glibc
process model's kernel) is open.
-/

@[expose] public section

namespace Silmaril.Elf.LpsCli.Sha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Problems
open Silmaril.Cli.Institution (Level Model Sen Out1)

/-- **`sha256sum-min` under LPS satisfies the standard sentence of `sha256sum` on stdin.** -/
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

/-- **`sha256sum-min` (static, LPS) and GNU `sha256sum` (glibc) agree run by run.** -/
theorem static_agrees_glibc {s : Silmaril.Cli.Bytes} {o o' : Out1} (h : staticModel.Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree staticModel_sat
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std h h'

/-- **The `sha256` filter under LPS satisfies its sentence.** -/
theorem filterModel_sat : filterModel.Sat (Sen.filter hexLine) := by
  refine sat_filter_of_prefix fun s oracle refusals limit en inp records tr hl ht => ?_
  obtain ⟨hp, hs, -, hv, he⟩ := hl
  rw [Sha256Cli.parsed, Option.some.injEq] at hp
  subst hp
  have hP := Sha256Cli.Registry.lpsPartial_solution oracle refusals limit en inp (lpsBytes s)
    ⟨hs, hv, he⟩
  have hpre := hP.safe tr ht
  simpa [hexLine, Sha256Cli.idealTrace, filterTrace] using hpre

/-- The GNU line is the filter's line with `"\n"` replaced by `"  -\n"`. -/
theorem sha256Stdin_eq_hexLine (s : Silmaril.Cli.Bytes) :
    Silmaril.Apps.Sha256sum.Sys.stdinRecord s =
      (hexLine s).dropLast ++ Silmaril.Apps.Sha256sum.lit "  -\n" := by
  have h := Sha256Cli.gnu_stdout (lpsBytes s)
  have h2 := congrArg cliBytes h
  simp only [cliBytes, List.map_map, List.map_append, List.map_dropLast] at h2
  simpa [hexLine, cliBytes, lpsBytes, Function.comp_def, Silmaril.Apps.Sha256sum.lit] using h2

end Silmaril.Elf.LpsCli.Sha256sum
