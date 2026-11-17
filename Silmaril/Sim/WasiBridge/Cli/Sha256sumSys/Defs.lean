module

public import Silmaril.Sim.WasiBridge.Sys.Defs
public import Silmaril.Sim.WasiBridge.Cli.Defs
public import Silmaril.Wasi.Cli.Institution.Defs
public import Silmaril.Cli.Institution.Std.Defs
public import Silmaril.Apps.Sha256sum.Plan

/-!
# sha256sum: a WASI reference program, a pinned WASI module, x86 builds (definitions)

Every model here is indexed by the standard input `s` and read at level `L1`; the meeting point
is `Std.sha256Stdin` (`hex(SHA-256(s)) ++ "  -\n"`, exit `0`).

**The worlds.** `stdinWorld s`: `sha256sum` with no operand, stdin `s`, no file system, stdout
not full: the domain `Sys.StdinDom` of silmaril's stage S1.

**The reference program, two readings** (`Silmaril.Sim.WasiBridge.Sys`):
* `refObs`: the observable traces of silmaril's reference program `Sys.refMachine` (read fd 0 in
  32768-byte requests to the end, write the record with retries, close 0, 1, 2, exit 0);
* `refP1`: the same program as a **WASI preview1 program**, through the `sys2wasi` adapter
  (`fd_read`, `fd_write`, `fd_close`, `proc_exit`). This is the WASI sha256sum whose sentence is
  proved (`Thms.wasiSha256_ref`), and the target of the equivalences below.

**A pinned WASI module.** `examples/wasi-sha256sum/dist/sha256sum.wasm` (`wasmFile`): a 2092-byte
core module, no libc, whose only imports are `wasi_snapshot_preview1.{fd_read, fd_write,
fd_close, proc_exit}`, written to make the reference program's calls in the same order. The
trace semantics of a core module against a preview1 host is not yet a definition here, so its
semantics is a parameter `W : Bytes → P1Sem`, and `Task.wasiRefinesRef W` states that it refines
`refP1`.

**x86 builds.**
* `minObs r11Of`: silmaril's x86 process model of its static, libc-free `sha256sum-min` (gcc
  13.3 `-O2`; `Sys.x86Machine`, loaded by `X86Sys.Init`). silmaril states, and does not prove,
  that it trace-refines the reference program (`Plan.S1Refines`; blocked on 8-bit ALU forms in
  `X86.Ext`).
* An ELF in the simulator stack, or under LPS (`elfModel`), given as observable traces
  `P : Bytes → List Obs → Prop`: **`Task.simSha256sumEquiv P`** states that it is
  `ElfWasiEquiv` to `refP1` for every stdin. `Task.sha256Stack P` asks for a whole layer stack
  (ELF, bytes simulator, P-calls, L form, adapted, WASI) ending at `refP1`.
* The native glibc or musl binary under its own process model (a full CLI model `M`, e.g.
  `Dyn.Program.x86Model` of GNU `sha256sum`): connected through `Task.nativeInTraces M P`
  (`Silmaril.Sim.WasiBridge.Cli`).

**Components.** `Task.componentSha256 σ T V`: a `wasi:cli` component's `wasiModel` meets the
lifted sentence. No bridge from preview1 programs to components is stated here.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Sha256sumSys

open Silmaril.Sim.WasiBridge.Sys
open Silmaril.Apps.Sha256sum (Bytes World lit)
open Silmaril.Apps.Sha256sum.Sys (refMachine WorldStep StdinDom)
open Silmaril.Cli.Institution (Level Model)

/-- **The world of a standard input**: no operand, no file system, stdout not full. -/
def stdinWorld (s : Bytes) : World :=
  { argv := [lit "sha256sum"], fs := fun _ => .openErr .ENOENT, stdin := .bytes s }

/-- The reference program's initial state. -/
def refInit : World → refMachine.State → Prop := fun _ st => st = .reading []

/-- **The reference program as observable traces.** -/
def refObs : Bytes → List Obs → Prop := machObs refMachine WorldStep refInit stdinWorld

/-- **The reference program as a WASI preview1 program.** -/
def refP1 : Bytes → P1Sem := machP1 refMachine WorldStep refInit stdinWorld

/-- **silmaril's `sha256sum-min` under its x86 process model**, as observable traces. -/
def minObs (r11Of : Silmaril.X86.State → Silmaril.X86.Word) : Bytes → List Obs → Prop :=
  machObs (Silmaril.Apps.Sha256sum.X86Sys.x86Machine r11Of) WorldStep
    (Silmaril.Apps.Sha256sum.X86Sys.Init Silmaril.Apps.Sha256sum.Binary.Image.image) stdinWorld

/-- The pinned module `examples/wasi-sha256sum/dist/sha256sum.wasm`: size and SHA-256. -/
structure WasmPin where
  path : String
  size : Nat
  sha256 : String

/-- `examples/wasi-sha256sum/dist/sha256sum.wasm` (Rust 1.99.1, `wasm32-unknown-unknown`, no
dependencies; `examples/wasi-sha256sum/build.sh`). -/
def wasmFile : WasmPin :=
  ⟨"examples/wasi-sha256sum/dist/sha256sum.wasm", 2092,
    "8aeedc3495370d82f08ef926a3da049f37dc28657218d4ba54a3a00b6c32b724"⟩

/-- **Task (a WASI sha256sum module refines the reference program)**: the preview1 traces `W s`
of a module run with stdin `s` (e.g. `wasmFile`) are, observably and within `S1`, traces of
`refP1 s`. -/
def Task.wasiRefinesRef (W : Bytes → P1Sem) : Prop :=
  ∀ s, Refines ((W s).obs S1) ((refP1 s).obs S1)

/-- **Task (an x86 sha256sum in the simulator ≡ the WASI sha256sum)**: the observable traces
`P s` of an x86 build (GNU `sha256sum` on glibc, a static musl build, `sha256sum-min`; run in
the WASM simulator stack or under LPS) are `ElfWasiEquiv` to the WASI reference program, for
every stdin. -/
def Task.simSha256sumEquiv (P : Bytes → List Obs → Prop) : Prop :=
  ∀ s, ElfWasiEquiv (P s) (refP1 s) S1

/-- **Task (a layer stack for sha256sum)**: per stdin, a stack from the ELF traces `P s` to the
WASI reference program. -/
def Task.sha256Stack (P : Bytes → List Obs → Prop) : Prop :=
  ∀ s, ∃ K : Stack, K.obs .elf = P s ∧ K.obs .wasi = (refP1 s).obs S1

/-- **Task (`sha256sum-min` is complete for the reference program)**: every observable trace of
the WASI reference program is one of the binary's. With `Plan.S1Refines` this makes the binary
`ElfWasiEquiv` to `refP1` (`Thms.min_equiv`). -/
def Task.minComplete (r11Of : Silmaril.X86.State → Silmaril.X86.Word) : Prop :=
  ∀ s, Refines ((refP1 s).obs S1) (minObs r11Of s)

/-- **Task (a `wasi:cli` component computes sha256sum)**: the component's CLI model meets the
standard sentence lifted to the full level. -/
def Task.componentSha256 {W : Silmaril.Wasi.World} {St : Type} (σ : W.Model)
    (T : Silmaril.Cli.Input → Silmaril.Wasm.Resource.Protocol St Silmaril.Wasi.WEv)
    (V : Silmaril.Wasi.Cli.View) : Prop :=
  (Silmaril.Wasi.Cli.wasiModel σ T V).Sat (Level.lift Silmaril.Cli.Institution.Std.sha256Stdin)

end Silmaril.Sim.WasiBridge.Sha256sumSys
