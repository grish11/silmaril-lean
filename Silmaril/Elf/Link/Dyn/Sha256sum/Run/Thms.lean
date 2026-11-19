module

public import Silmaril.Elf.Link.Dyn.Sha256sum.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinLoaded
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinLaws
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiLoaded
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.ExitPath
public import Silmaril.Raw.Elf.Link.Dyn.Imports.ShaRep
public import Silmaril.Raw.Elf.Link.Dyn.Imports.ShaState
public import Silmaril.Raw.Elf.Link.Dyn.Streams.Total
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitRunF
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MixedLoaded
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesErrSpec

/-!
# GNU `sha256sum` (coreutils 9.4, Ubuntu), end to end: theorems

* `Sha256sum.sha256sum_stdin` (stdin tier): for every `libcrypto.so.3`, `libc.so.6` and `ld.so`
  agreeing with the pinned chunks, every base, ifunc choice and binding mode, a process started
  by the kernel on the loaded image, in a world with the imports' contracts (`MainImps`,
  `TailImps`, `ExitOk`) whose library enters `main` with `argv = [a0]` and standard input `data`
  (`MainLib` at `World.atMain`), ends with the exit status and standard output of
  `Silmaril.Apps.Sha256sum.sha256sum` on that world, and nothing on stderr.
  `sha256sum_stdinK` asks `MainLib` only at the entries the start-up can produce.
* `Sha256sum.sha256sum_files` (`sha256sum F1 … Fn`, success tier): the same for readable files
  whose names are printed verbatim (`FilesSpec.Verbatim`); `sha256sum_filesK` likewise.
* `Sha256sum.sha256sum_mixed_loaded` (file-error tier, on the extended process `procG XG` that
  gnulib's `quotef` needs): each operand is readable and printed verbatim, or refused at `open`
  and gnulib-safe (`MOp`). Every run halts with the specification's status, standard output and
  standard error (`argv[0]: NAME: strerror(e)` per refused operand). The loader relation is
  `ExeLoadedP` (with the trusted loader fact `PageBase`). Unconditional: a readable operand
  keeps `program_invocation_name` (`MixedLoop.task_midPin`: the library calls keep the library's
  variables, `LibK`; `free` writes only the block it releases, `freeStep`/`FreeRet` with the live
  blocks in `Ghost.blocks`), a refused operand is `MixedErr.task_errStep`.
* `Imports.sha_contracts_satisfiable`: the `SHA256_*` contracts have a model.
* Resource preconditions (the total `malloc`/`fopen` contracts of `Streams.Defs`: `NULL` iff
  `allocOk = false` or the request is beyond `Env.maxAllocs/maxHeap/maxOpen/maxFile`):
  `sha256sum_stdin(K)` take `1 ≤ maxAllocs ∧ 0x8048 ≤ maxHeap`, `sha256sum_files(K)` on `n`
  operands take `n ≤ maxAllocs ∧ 0x8048 * n ≤ maxHeap ∧ n ≤ maxOpen`.

**Runs** (non-vacuity; `Sha256sum.Wit`): a concrete process meeting every hypothesis (the slot
stream representation `Streams.Total.slotRep`, every import bound to its contract, resource
bounds 4 allocations of 64 KiB in total and 4 open streams), from the kernel's state:

* `Wit.sha256sum_stdin_runs data (hd : 64 + data.length ≤ S0)`: a run of `sha256sum` on standard
  input `data` ends with status 0 and standard output `hex(SHA-256(data)) ++ "  -\n"`;
  `sha256sum_stdin_runs_spec`: the outcome is silmaril's `Silmaril.Apps.Sha256sum.sha256sum`.
* `Wit.sha256sum_files_runs d (hd : 64 + d.length ≤ S0)`: `sha256sum f`, `f` holding `d`, ends
  with status 0 and `hex(SHA-256(d)) ++ "  f\n"`; `sha256sum_files_runs_spec` likewise.
* `Wit.task_mainLibReach`: from every gate state the library can enter `main` with the kernel's
  kept memory (`MainLib`); the runs use `Proc.RunInv.must_run_of_inv` (a `Must` plus an invariant
  with local progress gives a run).

**Model limit** (a property of the model, not of `sha256sum`): `slotRep` holds a stream's unread
bytes in one 1 MiB slot, so the input fits `64 + |data| ≤ S0`.
**Trusted** (beyond the header of `Dyn`): the import contracts of `Streams.Defs`, `Imports.Defs`
and `Proc.Defs`, the stream representation `slotRep`, the concrete `Env`/`World` of `WitWorld`
and silmaril's specification.
-/
