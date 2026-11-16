module

public import Silmaril.Containers.Mini.Thms
public meta import Silmaril.Containers.Mini.Defs

/-!
# The minimal machine: executable checks

Checked by evaluation (`#guard`) when this module is built: the classification of task-creation
requests by their flags, and the runs `result` computes for the fixtures (`Thms.runs_iff`: they
are the runs of the machine). They evaluate the model; no system call is made.
-/

public section

namespace Silmaril.Containers.Mini.Examples

open Silmaril.Containers Silmaril.Containers.Mach

/-! ## Task creation, by flags -/

-- glibc's `pthread_create`: a thread.
#guard (CloneReq.clone 0x3d0f00).kind == .thread
-- `clone3` with `CLONE_VM | CLONE_THREAD | CLONE_SIGHAND`: a thread.
#guard (CloneReq.clone3 0x10900).kind == .thread
-- `CLONE_THREAD` alone (the kernel answers `EINVAL`): still classified a thread, conservatively.
#guard (CloneReq.clone CLONE_THREAD).kind == .thread
-- `vfork`, and `clone(CLONE_VM | CLONE_VFORK | SIGCHLD)` as glibc's `posix_spawn` makes it.
#guard CloneReq.vfork.kind == .sharedVm
#guard (CloneReq.clone (CLONE_VM ||| CLONE_VFORK ||| SIGCHLD)).kind == .sharedVm
-- `fork`, `clone(SIGCHLD)` and `clone3` with no flags: a process.
#guard CloneReq.fork.kind == .process
#guard (CloneReq.clone SIGCHLD).kind == .process
#guard (CloneReq.clone3 0).kind == .process
-- The sequential policy.
#guard (CloneReq.clone 0x3d0f00).ub == .threadCreate
#guard CloneReq.vfork.ub == .threadCreate
#guard CloneReq.fork.ub == .unmodeled
-- x86-64 system call numbers.
#guard [CloneReq.clone 0, .fork, .vfork, .clone3 0].map CloneReq.sysno == [56, 57, 58, 435]

/-! ## Runs of the fixtures -/

/-- How a finite run stopped. -/
def stop? : Beh Ev → Option Stop
  | .done _ s => some s
  | _ => none

/-- The run has no undefined behaviour (decidable form of `Spec.noUB`). -/
def noUB? : Beh Ev → Bool
  | .done _ (.undefined _) => false
  | _ => true

#guard stop? (result hello) == some (.exited 0)
#guard noUB? (result hello)
#guard stop? (result threadSpawn) == some (.undefined .threadCreate)
#guard stop? (result vforkExit) == some (.undefined .threadCreate)
#guard stop? (result forkExit) == some (.undefined .unmodeled)
#guard stop? (result fallOff) == some (.undefined .stuck)
#guard !noUB? (result threadSpawn) && !noUB? (result fallOff)
-- Spinning: no undefined behaviour, and no stop.
#guard noUB? (result spinForever) && stop? (result spinForever) == none
-- A thread request after output: the output is kept, then undefined behaviour.
#guard stop? (result (.emit (.stdout [1]) :: threadSpawn)) == some (.undefined .threadCreate)

end Silmaril.Containers.Mini.Examples
