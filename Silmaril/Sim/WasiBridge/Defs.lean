module

public import Silmaril.Wasi.Versions.P1.Os.Thms

/-!
# ELF ≡ WASI: syscall ↔ WASI adapters and trace equivalence (definitions)

Groundwork for proving an x86-64 ELF binary, run in the simulator stack with a syscall → WASI
adapter, equivalent to a WASI program (runtime:
`examples/wasm-sim/wasi-bridge`).

**Signatures.**
* `SysName`, `Subset`, `S1`: syscall subsets (x86-64 Linux numbers `SysName.nr`); the runtime
  adapter `sys2wasi.wat` implements `S1`.
* `SysEv`: a *lifted* syscall event (buffers as bytes, as `Silmaril.Wasi.Versions.P1` lifts WASI p1
  events): `read fd n data`, `write fd data k`, `exit code`.
* `Obs`: the observable alphabet shared by both sides: bytes read from / written to a
  descriptor, and the exit status. `obsOfEvent`: an LPS `Event` (the process side,
  `Silmaril.Machine.Process.IoSpec`) as observables (the file system at exit is forgotten).

**The adapter as a translation of signatures** (a map of event alphabets, the comorphism's
sentence part; the strategy part is the runtime module):
* `toP1 : SysEv → List WEv`: write ↦ `fd_write(fd, [data]) = ok k`, read ↦ `fd_read(fd, [n]) =
  ok data`, exit ↦ `proc_exit code` (unanswered), in the lifted preview1 events of
  `Silmaril.Wasi.Versions.P1` (`wasi2sys.wat` is the reverse direction, `ofP1`);
* `p1Obs : WEv → List Obs`: the observable image of a lifted p1 answer (`P1.osEv` generalised to
  every descriptor, reads and exit); `sysObs : SysEv → List Obs`.

**Trace semantics.**
* Processes: `ProcRun step E m e tr`: a finite run of the deterministic user step `step` from `m`
  with syscall environment `E` (`IoSpec.SysEnv`: answers `IoOut.resume`/`halt` at `syscall`
  traps) emitting the LPS events `tr`. `procObs` its observable traces.
* WASI p1 programs: `P1Sem` = a set of lifted host-answer traces (the `hostView` of the
  program's plays against a p1 host). The concrete semantics of a core module against the
  preview1 theory `P1.th` is a parameter here (`notes`: Task).

**The target.** `ElfWasiEquiv P W S`: the observable traces of the process `P` are exactly the
images of the WASI traces of `W` that stay within the image of the subset `S` (`InP1 S`).
`Equiv`/`Refines` on observable trace sets compose (`Refines.trans`, `Equiv.trans`); a `Stack`
lists the layers (ELF on the bytes-decoding simulator → P-calls → L-form → adapter → WASI) with
an equivalence per edge; `Stack.equiv` composes them (`Thms`).
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge

open Silmaril.Wasi (WEv)
open Silmaril.Wasi.Versions.P1 (fn okAns iovBytes)
open Silmaril.Wasm.Component (Val)
open Silmaril.Process.LPS (Event Word)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.X86 (MState)
open Silmaril.Process.LPS.Machines

/-! ## Syscall subsets -/

/-- Syscalls of the bridge. -/
inductive SysName where
  | read | write | exit | exitGroup | brk
  deriving DecidableEq, Repr

/-- x86-64 Linux numbers. -/
def SysName.nr : SysName → Nat
  | .read => 0 | .write => 1 | .exit => 60 | .exitGroup => 231 | .brk => 12

/-- A syscall subset (the signature of a process's environment). -/
abbrev Subset := List SysName

/-- `S₁`: stdio and exit (`examples/wasm-sim/wasi-bridge/wat/sys2wasi.wat`). -/
def S1 : Subset := [.read, .write, .exit, .exitGroup, .brk]

/-- A lifted syscall event. -/
inductive SysEv where
  /-- `read(fd, buf, n)` returned `data` (`|data| ≤ n`). -/
  | read (fd n : Nat) (data : List (BitVec 8))
  /-- `write(fd, data)` wrote the first `k` bytes. -/
  | write (fd : Nat) (data : List (BitVec 8)) (k : Nat)
  /-- `exit_group(code)`. -/
  | exit (code : Nat)
  deriving DecidableEq, Repr

/-- The syscall of an event (`exit` stands for `exit` and `exit_group`). -/
def SysEv.name : SysEv → SysName
  | .read .. => .read | .write .. => .write | .exit _ => .exitGroup

/-- Events of the subset `S`. -/
def SysEv.In (S : Subset) (e : SysEv) : Prop := e.name ∈ S

/-! ## Observables -/

/-- The observable alphabet of both sides. -/
inductive Obs where
  | rd (fd : Nat) (b : BitVec 8)
  | wr (fd : Nat) (b : BitVec 8)
  | exit (code : Nat)
  deriving DecidableEq, Repr

/-- The observables of an LPS event (channels read as descriptors; the file system is dropped). -/
def obsOfEvent : Event → List Obs
  | .readEv ch b => [.rd ch.toNat b]
  | .writeEv ch b => [.wr ch.toNat b]
  | .exitEv code _ => [.exit code.toNat]
  | .killEv .. => []

/-- The observables of an LPS trace. -/
def obsTrace (tr : List Event) : List Obs := tr.flatMap obsOfEvent

/-- The observables of a lifted syscall event (exit status modulo 256, as Linux reports it). -/
def sysObs : SysEv → List Obs
  | .read fd _ data => data.map (.rd fd)
  | .write fd data k => (data.take k).map (.wr fd)
  | .exit code => [.exit (code % 256)]

/-! ## The adapter: syscalls ↔ lifted WASI preview1 events -/

/-- **syscall → WASI p1** (`sys2wasi.wat`), on lifted events. -/
def toP1 : SysEv → List WEv
  | .write fd data k =>
    [.imp (fn "fd_write") [.u32 (BitVec.ofNat 32 fd), .record [Silmaril.Wasi.bytesV data]]
      (okAns (some (.u32 (BitVec.ofNat 32 k))))]
  | .read fd n data =>
    [.imp (fn "fd_read") [.u32 (BitVec.ofNat 32 fd), .record [.u32 (BitVec.ofNat 32 n)]]
      (okAns (some (Silmaril.Wasi.bytesV data)))]
  | .exit code => [.imp (fn "proc_exit") [.u32 (BitVec.ofNat 32 (code % 256))] none]

/-- `toP1` on traces. -/
def toP1Trace (t : List SysEv) : List WEv := t.flatMap toP1

/-- **WASI p1 → syscall** (`wasi2sys.wat`), on lifted events: single-iovec `fd_write`/`fd_read`
answered `ok`, and `proc_exit`; anything else has no syscall image. -/
def ofP1 : WEv → List SysEv
  | .imp f [.u32 fd, .record [buf]] (some [.variant 0 (some v)]) =>
    if f = fn "fd_write" then
      match v with
      | .u32 k => [.write fd.toNat (Silmaril.Wasi.bytesOf buf) k.toNat]
      | _ => []
    else if f = fn "fd_read" then
      match buf with
      | .u32 n => [.read fd.toNat n.toNat (Silmaril.Wasi.bytesOf v)]
      | _ => []
    else []
  | .imp f [.u32 code] none => if f = fn "proc_exit" then [.exit code.toNat] else []
  | _ => []

/-- The observable image of a lifted p1 answer. -/
def p1Obs (e : WEv) : List Obs := (ofP1 e).flatMap sysObs

/-- A lifted p1 trace stays within the image of the subset `S`. -/
def InP1 (S : Subset) (t : List WEv) : Prop := ∀ e ∈ t, ∀ s ∈ ofP1 e, s.In S

/-! ## Trace semantics -/

/-- **Finite runs of a process**: user steps of `step`, and at a `syscall` trap any answer of
the environment `E` (for some flag completion `ch`), emitting LPS events. -/
inductive ProcRun (step : MState → Option MState) (E : SysEnv) : MState → E.Model → List Event → Prop
  | stop (m : MState) (e : E.Model) : ProcRun step E m e []
  | step {m m' : MState} {e : E.Model} {tr : List Event} : step m = some m' →
      ProcRun step E m' e tr → ProcRun step E m e tr
  | resume {m m' : MState} {e e' : E.Model} {ch : X86FlagChoices.Choice} {evs tr : List Event} :
      AtSyscall m → E.arm (trapped ⟨m, none⟩ ch) e (.resume m' e' evs) →
      ProcRun step E m' e' tr → ProcRun step E m e (evs ++ tr)
  | halt {m : MState} {e : E.Model} {ch : X86FlagChoices.Choice} {evs : List Event} :
      AtSyscall m → E.arm (trapped ⟨m, none⟩ ch) e (.halt evs) → ProcRun step E m e evs

/-- The observable traces of a process. -/
def procObs (step : MState → Option MState) (E : SysEnv) (m : MState) (e : E.Model) :
    List Obs → Prop :=
  fun o => ∃ tr, ProcRun step E m e tr ∧ obsTrace tr = o

/-- A WASI preview1 program's semantics: its lifted host-answer traces (prefix-closed). -/
structure P1Sem where
  traces : List WEv → Prop

/-- The observable traces of a WASI program within the subset `S`: prefixes of the images of its
traces (observables are byte-granular, as LPS events are; a WASI `fd_write` is one event). -/
def P1Sem.obs (W : P1Sem) (S : Subset) : List Obs → Prop :=
  fun o => ∃ t, W.traces t ∧ InP1 S t ∧ o <+: t.flatMap p1Obs

/-! ## Equivalence and the layer stack -/

/-- Trace refinement of observable trace sets. -/
def Refines (lo hi : List Obs → Prop) : Prop := ∀ o, lo o → hi o

/-- Trace equivalence. -/
def Equiv (A B : List Obs → Prop) : Prop := Refines A B ∧ Refines B A

/-- **The target**: the process `P` is equivalent to the WASI program `W` modulo the adapter,
for the syscall subset `S`. -/
def ElfWasiEquiv (P : List Obs → Prop) (W : P1Sem) (S : Subset) : Prop := Equiv P (W.obs S)

/-- The layers between an ELF binary and a WASI program. -/
inductive Layer where
  /-- The ELF on the reference machine with an LPS syscall environment (`ProcRun`). -/
  | elf
  /-- The ELF on the bytes-decoding simulator (P-mem) with the `sys2wasi` syscall layer. -/
  | bytesSim
  /-- The program-as-calls translation (P-calls) of the binary. -/
  | pcalls
  /-- The L form (registers as locals, methods inlined). -/
  | lform
  /-- The L form with the syscall imports replaced by the WASI adapter (a WASI p1 module). -/
  | adapted
  /-- The hand-written / compiled WASI program. -/
  | wasi
  deriving DecidableEq, Repr

/-- The layers, in order. -/
def layers : List Layer := [.elf, .bytesSim, .pcalls, .lform, .adapted, .wasi]

/-- A stack: the observable traces of every layer and an equivalence per consecutive pair. -/
structure Stack where
  obs : Layer → List Obs → Prop
  edge : ∀ i (h : i + 1 < layers.length),
    Equiv (obs (layers[i]'(by omega))) (obs (layers[i + 1]'h))

/-! ## Hello world -/

/-- The preview1 `hello` (`fd_write(1, "hi") = ok 2; proc_exit 0`) as a WASI program: the
prefixes of `Silmaril.Wasi.Versions.P1.helloP1`. -/
def helloP1Sem : P1Sem := ⟨fun t => t <+: Silmaril.Wasi.Versions.P1.helloP1⟩

/-- **Task (hello, the converse)**: every proved x86 `hello` runtime (`HelloLoop`, e.g. the
42-byte program of `Silmaril.Wasi.Runtime`) on stdout channel `1` is *equivalent* to the preview1
`hello`: `helloLoop_refines` (`Thms`) is the inclusion process ⊆ WASI; open is that every
WASI-side observable prefix is produced (progress of the runtime under `lpsEnv`). -/
def Task.helloEquiv : Prop :=
  ∀ (c : MState → Option MState) (segs : List Silmaril.Process.LPS.Segment)
    (e : Silmaril.Process.LPS.Model) (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e),
    (∀ m, AtSyscall m → c m = none) →
    ElfWasiEquiv (procObs c (lpsEnv segs) R.start e) helloP1Sem S1

/-- **Task (the end goal for one program)**: a stack from the ELF layer to a WASI layer exists
for the simulator-run `hello` of `examples/wasm-sim/wasi-bridge` (ELF `progs/hello`, WASI
`progs/hello-wasi.wat`), given the semantics of each layer: `elfObs` (the ELF under LPS launch),
`wasiObs` (the WASI module against the preview1 theory). Stated over those semantics until the
launch of an ELF file and the core-Wasm-with-p1-host trace semantics are definitions here. -/
def Task.helloStack (elfObs : List Obs → Prop) (wasi : P1Sem) : Prop :=
  ∃ K : Stack, K.obs .elf = elfObs ∧ K.obs .wasi = wasi.obs S1

end Silmaril.Sim.WasiBridge
