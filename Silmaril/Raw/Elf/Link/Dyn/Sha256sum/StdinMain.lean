module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailPost
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.ExitPath

/-! # GNU `sha256sum`, stdin tier: `main` to the end of the process, without open goals

`task_mainStdinTail` proves `Task.mainStdinTail` (`tail_pre` then `tail_post`), and with
`task_exitPath` (`Task.exitPath`) `sha_main_stdin_ok` / `sha_main_stdin_spec_ok` are
`sha_main_stdin` / `sha_main_stdin_spec` with no task left: what remains are the
assumptions on the world (`MainImps`, `TailImps`, `ExitOk`: the imports' contracts and the
library's guarantees) and on `main`'s entry state (`MainEntryS`, `TailEntry`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

/-- **`Task.mainStdinTail` is proved** (from the world's `TailImps`). -/
theorem task_mainStdinTail {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (T : TailImps E R W b lb kb sc) : Task.mainStdinTail E W b lb kb sr sc := by
  intro C fi data Q s s1 z g ht hO hout hjobs hres _ hargc k
  exact tail_pre T.dig.dig.cl.img T.dig.dig.cl.hb T.optA ht hO hargc fun v hv => tail_post T ht hv hout hjobs hres k

/-- **sha256sum, stdin tier, from `main`'s entry** (no open goal): every run ends with status 0
having written `stdinLine data`. -/
theorem sha_main_stdin_ok {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (T : TailImps E R W b lb kb sc) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {s : PState} {a0p : Word} {a0 data : List Byte} {g : Word}
    (h : MainEntryS E W b lb kb sr sc C fi s a0p a0 data g) (ht : TailEntry E W b lb s fi g) :
    MustQ W (Ended 0 fun w => w = stdinLine data) s :=
  sha_main_stdin I (task_mainStdinTail T) task_exitPath XO h ht

/-- **sha256sum, stdin tier, against the specification** `Apps.Sha256sum.sha256sum` (no open
goal): the run's exit status and standard output are the specification's. -/
theorem sha_main_stdin_spec_ok {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word}
    (I : MainImps E W b lb sr) (T : TailImps E R W b lb kb sc) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {s : PState} {a0p : Word} {a0 data : List Byte} {g : Word}
    (h : MainEntryS E W b lb kb sr sc C fi s a0p a0 data g) (ht : TailEntry E W b lb s fi g) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stderr = []) s :=
  sha_main_stdin_spec I (task_mainStdinTail T) task_exitPath XO h ht posix fs

end Silmaril.Elf.Link.Dyn.Sha256sum
