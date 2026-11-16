module

public import Silmaril.Containers.Machine.Defs
public import Silmaril.Containers.Fixtures.Defs

/-!
# A minimal machine: undefined behaviour and thread creation, under a sequential machine

`mini` is a machine semantics (`Silmaril.Containers.Mach.MachineSem`) for straight-line
programs (`Instr`): emit an event, request a task (`clone`), exit, crash, or spin. Its state is
the rest of the program. Running off the end of a program is a **stuck** state, so it is
undefined behaviour, not an absence of runs; a `clone` request is undefined behaviour or
`unmodeled` under the sequential policy (`CloneReq.ub`).

`machRT` is the runtime model: the entry-point shape over images whose files are programs, and
`mini`'s runs. Like `Fixtures.small`, it is a model, not a system: no instruction set, no system
call numbers are decoded; a `clone` instruction stands for whichever system call an instance
maps to it.

| Program | Its run | `wlp` | `wp` |
| --- | --- | --- | --- |
| `hello`: print `hi`, exit 0 | `done [stdout "hi"] (exited 0)` | yes | yes |
| `threadSpawn`: `clone` with `pthread_create`'s flags, exit 0 | `done [] (undefined threadCreate)` | no | no |
| `vforkExit`: `vfork`, exit 0 | `done [] (undefined threadCreate)` | no | no |
| `forkExit`: `fork`, exit 0 | `done [] (undefined unmodeled)` | no | no |
| `fallOff`: print `x`, then nothing | `done [stdout "x"] (undefined stuck)` | no | no |
| `spinForever` | `spins []` | yes | no |

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Mini

open Silmaril.Containers Silmaril.Containers.Mach

/-- **Instructions** of the minimal machine. -/
inductive Instr where
  | emit (e : Ev)
  | clone (r : CloneReq)
  | exit (c : UInt8)
  | crash (sig : Nat)
  | spin
  deriving DecidableEq, Repr

/-- **The minimal machine**: the state is the rest of the program. -/
abbrev mini : MachineSem (List Instr) Ev where
  State := List Instr
  isIn := Ev.isInput
  load p s := s = p
  step s a s' :=
    match s with
    | .emit e :: rest => a = .ev e ∧ s' = rest
    | .clone r :: rest => a = .clone r ∧ s' = rest
    | .spin :: _ => a = .tau ∧ s' = s
    | _ => False
  final s st :=
    match s with
    | .exit c :: _ => st = .exited c
    | .crash g :: _ => st = .signaled g
    | _ => False

/-- An event in front of a finite run. -/
def cons (e : Ev) : Beh Ev → Beh Ev
  | .done t s => .done (e :: t) s
  | .blocked t => .blocked (e :: t)
  | .spins t => .spins (e :: t)
  | .reactive f => .reactive fun n => if n = 0 then e else f (n - 1)

/-- **The run of a program that emits no input event.** -/
def result : List Instr → Beh Ev
  | [] => .done [] (.undefined .stuck)
  | .emit e :: p => cons e (result p)
  | .clone r :: _ => .done [] (.undefined r.ub)
  | .exit c :: _ => .done [] (.exited c)
  | .crash g :: _ => .done [] (.signaled g)
  | .spin :: _ => .spins []

/-- The program emits no input event. -/
def OutputOnly (p : List Instr) : Prop := ∀ e, Instr.emit e ∈ p → e.isInput = false

/-- **The runtime model over the minimal machine**: the program at the entry point. -/
def machRT : Runtime (Flat (List Instr)) (List Instr) Ev :=
  Runtime.ofShape (Shape.entry .static some) mini.runs

/-- An image with the program `p` at `/app`. -/
def mimage (p : List Instr) : Flat (List Instr) where
  config := { entrypoint := ["/app"] }
  root := Tree.empty.set ["app"] (some (.file p true))

def hello : List Instr := [.emit (.stdout (Fixtures.ascii "hi")), .exit 0]
def threadSpawn : List Instr := [.clone (.clone 0x3d0f00), .exit 0]
def vforkExit : List Instr := [.clone .vfork, .exit 0]
def forkExit : List Instr := [.clone .fork, .exit 0]
def fallOff : List Instr := [.emit (.stdout (Fixtures.ascii "x"))]
def spinForever : List Instr := [.spin]

end Silmaril.Containers.Mini
