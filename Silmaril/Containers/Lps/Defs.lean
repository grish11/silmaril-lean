module

public import Silmaril.Containers.Machine.Defs
public import Silmaril.Process.LPS.Problems.CoreutilsLite.Spec
public import Silmaril.Process.LPS.ELFImageX86
public import Silmaril.Containers.Oci.Defs

/-!
# The Linux process semantics as a container machine (restricted, sequential)

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

`lps` reads the Linux process semantics of `Silmaril.Process.LPS` (LPS) for statically linked
x86-64 programs as a machine semantics of `Silmaril.Containers.Mach`, so that a container
runtime over it (`Mach.MachRuntime`) has explicit undefined behaviour, events and task creation.

**What a state is.** An LPS configuration (`Config`) of the x86-64 machine with a flag oracle
(`Machines.x86WithFlagOracle oracle`), the program's segments, the events read off LPS steps that
are not yet emitted (`pending`), and whether the run has reached undefined behaviour (`bad`).

**Initial states** (`lps.load snapshot`): for every flag oracle, every allocation limit, and every
launch LPS admits (`CoreutilsLite.Admissible`: a valid input, that is argv, environment, stdin,
file system, and a valid entry, that is stack pointer, brk and mmap base), the LPS initial
configuration (`X86Launch.init`). Quantifying over every oracle covers every resolution of the
flags x86-64 leaves undefined (AF after `xor`, for example); quantifying over every admissible
launch covers every launch the runtime may perform. Admissibility is the **trust boundary with
the runtime**: a runtime that launches the program outside it (an invalid stack, an
inaccessible entry) is not described.

**Steps.**

* LPS steps of the reference semantics (`SStep` with the native x86-64 system call table
  `Probes.spec` and no refusal filter, LPS's `run`) are internal steps; their events become
  pending events (`mapEvs`) emitted one by one: bytes read on channel 0 are `Ev.stdin`, bytes
  written on channels 1 and 2 are `Ev.stdout` and `Ev.stderr`, bytes read and written on a TCP
  connection (LPS channel `3 + k` for the `k`-th accepted connection) are `Ev.recv` and
  `Ev.send` on `connSock`, and an exit or kill event is dropped (it is the run's stop). LPS
  reports no event for `socket`, `bind`, `listen` or `accept` themselves (they change its
  descriptor table), so neither does the adapter. **Any other event** is outside this adapter:
  the run ends in `undefined unmodeled`, a statement that the adapter makes no claim, never a
  silent success.
* An LPS step to an error is undefined behaviour: `unmodeled` when LPS marks the step unmodelled
  (`UnmodeledAt`: an instruction or a system call outside LPS's model), `memory` otherwise (a
  machine fault, a failed materialisation of system call accesses). A configuration with no LPS
  step that has not halted has no adapter step either, so the run ends in `undefined stuck`
  (`Mach.MachineSem.Run.stuck`).
* **Task creation is explicit and overrides LPS.** At a configuration whose pending system call is
  `clone` (56), `fork` (57), `vfork` (58) or `clone3` (435), the only step is the action
  `clone r` (`cloneReq`); LPS's own reading of these calls (which models `clone(SIGCHLD)` and
  `fork` as returning a pid without a child) is never used. Under `seqPolicy` every such run ends
  in undefined behaviour (`threadCreate` or `unmodeled`). The flags of `clone` are its first
  argument; those of `clone3` are the first 8 bytes of its `struct clone_args`, read through the
  ISA's byte view; when they are not readable they are taken as `CLONE_THREAD`, which can only
  change the reason, since every request is undefined behaviour under `seqPolicy`.

**Stops.** A halted configuration with no kill is `exited (code mod 256)`; a killed one is
`signaled`.

**Trusted.** The LPS transcription of Linux system calls, the x86-64 decoder and instruction
semantics behind `x86WithFlagOracle`, and the admissibility of launches. Not modelled: threads
(task creation is undefined behaviour), signals sent by others, time, and every event outside the
three standard channels and LPS's TCP connections. LPS itself models AF_INET stream sockets only,
and `bind` only to port 0 (any other port is `unmodeled`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Lps

open Silmaril.Containers Silmaril.Containers.Mach
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines

/-- A flag oracle: how each undefined flag is resolved, step by step. -/
abbrev Oracle : Type := Nat → X86FlagChoices.Choice

/-- The x86-64 machine with a flag oracle. -/
abbrev isaOf (o : Oracle) : UserIsa := x86WithFlagOracle o

/-! ## Task creation -/

/-- The four task-creation system call numbers. -/
def cloneNumber (x8 : Word) : Bool := x8 == 56 || x8 == 57 || x8 == 58 || x8 == 435

/-- A 64-bit little-endian value read through an ISA's byte view, if every byte is readable. -/
def readU64 (isa : UserIsa) (segs : List Segment) (ms : isa.State) (addr : Word) :
    Option UInt64 :=
  ((List.range 8).mapM fun i => isa.readByte segs ms (addr + BitVec.ofNat 64 i)).map fun bs =>
    (bs.foldr (fun (b : BitVec 8) acc => acc * 256 + b.toNat) 0).toUInt64

/-- **The task-creation request** of a pending system call, if it is one. -/
def cloneReq (isa : UserIsa) (segs : List Segment) (ms : isa.State) (x8 : Word) :
    Option CloneReq :=
  let arg0 := (isa.syscallArgs ms).headD 0
  if x8 = 56 then some (.clone arg0.toNat.toUInt64)
  else if x8 = 57 then some .fork
  else if x8 = 58 then some .vfork
  else if x8 = 435 then some (.clone3 ((readU64 isa segs ms arg0).getD CLONE_THREAD))
  else none

/-- A configuration is about to create a task. -/
def ClonePending {isa : UserIsa} (c : Silmaril.Process.LPS.Config isa) : Prop :=
  c.model.halted = none ∧ ∃ x8, isa.svcPending c.ms = some x8 ∧ cloneNumber x8 = true

/-! ## Events -/

/-- **The connection of a trace channel.** LPS reports the octets of its `k`-th accepted TCP
connection (AF_INET, stream) on channel `3 + k` (`connChannel`); the adapter names that
connection by its channel. -/
def connSock (ch : Word) : Sock := ⟨ch.toNat, .inet4, .stream⟩

/-- The container event of an LPS event: `some evs` for the standard channels, the TCP
connections (channels from 3: octets read are `Ev.recv`, octets written are `Ev.send`) and the
stop events (which are dropped). -/
def mapEv : Event → Option (List Ev)
  | .readEv ch b =>
    if ch = 0 then some [.stdin [UInt8.ofBitVec b]]
    else if 3 ≤ ch.toNat then some [.recv (connSock ch) [UInt8.ofBitVec b]] else none
  | .writeEv ch b =>
    if ch = 1 then some [.stdout [UInt8.ofBitVec b]]
    else if ch = 2 then some [.stderr [UInt8.ofBitVec b]]
    else if 3 ≤ ch.toNat then some [.send (connSock ch) [UInt8.ofBitVec b]] else none
  | .exitEv _ _ | .killEv _ _ => some []

/-- The container events of a list of LPS events, if all are supported. -/
def mapEvs (evs : List Event) : Option (List Ev) := (evs.mapM mapEv).map List.flatten

/-! ## The machine -/

/-- **A state of the adapter.** -/
structure St where
  oracle : Oracle
  segs : List Segment
  cfg : Silmaril.Process.LPS.Config (isaOf oracle)
  pending : List Ev
  bad : Option UB

/-- The LPS reference semantics the adapter steps with. -/
abbrev LStep (sp : Sys SyscallEffect) (s : St) (evs : List Event) (t : StepTo (isaOf s.oracle)) :
    Prop :=
  SStep s.segs sp noFilter s.cfg evs t

/-- **The steps of the adapter.** -/
inductive Step (sp : Sys SyscallEffect) : St → Act Ev → St → Prop where
  /-- Emit a pending event. -/
  | emit {s : St} {e : Ev} {rest : List Ev} (h : s.pending = e :: rest) :
      Step sp s (.ev e) { s with pending := rest }
  /-- An LPS step whose events are supported. -/
  | lps {s : St} {evs : List Event} {c' : Silmaril.Process.LPS.Config (isaOf s.oracle)} {es : List Ev}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep sp s evs (.next c')) (hm : mapEvs evs = some es) :
      Step sp s .tau { s with cfg := c', pending := es }
  /-- An LPS step with an event outside the adapter: no claim. -/
  | unsupported {s : St} {evs : List Event} {c' : Silmaril.Process.LPS.Config (isaOf s.oracle)}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep sp s evs (.next c')) (hm : mapEvs evs = none) :
      Step sp s .tau { s with bad := some .unmodeled }
  /-- An LPS error at an unmodelled instruction or system call. -/
  | unmodeled {s : St} {evs : List Event}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep sp s evs .error) (hu : UnmodeledAt s.segs sp s.cfg) :
      Step sp s .tau { s with bad := some .unmodeled }
  /-- Any other LPS error (a fault). -/
  | fault {s : St} {evs : List Event}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep sp s evs .error) (hu : ¬ UnmodeledAt s.segs sp s.cfg) :
      Step sp s .tau { s with bad := some .memory }
  /-- A task-creation request: the clone policy decides. -/
  | clone {s : St} {x8 : Word} {r : CloneReq}
      (hp : s.pending = []) (hb : s.bad = none) (hh : s.cfg.model.halted = none)
      (hx : (isaOf s.oracle).svcPending s.cfg.ms = some x8) (hn : cloneNumber x8 = true)
      (hr : cloneReq (isaOf s.oracle) s.segs s.cfg.ms x8 = some r) :
      Step sp s (.clone r) s

/-- **How a state stops.** -/
inductive Final : St → Stop → Prop where
  | undefined {s : St} {u : UB} (hp : s.pending = []) (hb : s.bad = some u) :
      Final s (.undefined u)
  | exited {s : St} {code : Word} (hp : s.pending = []) (hb : s.bad = none)
      (hh : s.cfg.model.halted = some code) (hk : s.cfg.model.killedBy = none) :
      Final s (.exited (code.toNat % 256).toUInt8)
  | signaled {s : St} {sig : Word} (hp : s.pending = []) (hb : s.bad = none)
      (hk : s.cfg.model.killedBy = some sig) :
      Final s (.signaled sig.toNat)

/-- The initial state of one launch. -/
def St.init (snap : X86Launch.Snapshot) (o : Oracle) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) : St :=
  ⟨o, snap.image.segments, X86Launch.init (isaOf o) snap en limit inp, [], none⟩

/-- **The adapter over a system call table** `sp`: LPS for a loaded x86-64 snapshot, as a
container machine, with LPS's steps taken under `sp`. -/
abbrev lpsWith (sp : Sys SyscallEffect) : MachineSem X86Launch.Snapshot Ev where
  State := St
  isIn := Ev.isInput
  load snap s := ∃ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp ∧
    s = St.init snap o limit en inp
  step := Step sp
  final := Final

/-- **The adapter**: the reference semantics, LPS's native x86-64 table `Probes.spec`. -/
abbrev lps : MachineSem X86Launch.Snapshot Ev := lpsWith Probes.spec

/-! ## Programs that only exit -/

/-- An exit or kill event. -/
def IsStop : Event → Prop
  | .exitEv _ _ | .killEv _ _ => True
  | _ => False

/-- Only stop events. -/
def StopOnly (tr : List Event) : Prop := ∀ e ∈ tr, IsStop e

/-- **Exit-only**: only stop events, then a halt with status `k` and no kill. -/
def Post {o : Oracle} (k : Word) : Omni.Post (isaOf o) := fun tr out =>
  StopOnly tr ∧ ∃ final, out = .halt final ∧ final.model.killedBy = none ∧ final.model.halted = some k

/-- No reachable configuration is about to create a task, under the table `sp`. -/
def NoCloneFromWith (sp : Sys SyscallEffect) {isa : UserIsa} (segs : List Segment)
    (c : Silmaril.Process.LPS.Config isa) : Prop :=
  ∀ tr c', Star segs sp noFilter c tr c' → ¬ ClonePending c'

/-- No reachable configuration is about to create a task, under the native table. -/
abbrev NoCloneFrom {isa : UserIsa} (segs : List Segment) (c : Silmaril.Process.LPS.Config isa) :
    Prop :=
  NoCloneFromWith Probes.spec segs c

/-- The hypotheses: every admissible launch of `snap` only exits, with status `k`, and never
reaches a task-creation request. -/
structure ExitOnly (snap : X86Launch.Snapshot) (k : Word) : Prop where
  exec : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    Omni.Exec snap.image.segments Probes.spec noFilter (X86Launch.init (isaOf o) snap en limit inp)
      (Post k)
  noClone : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    NoCloneFrom snap.image.segments (X86Launch.init (isaOf o) snap en limit inp)
  launch : ∃ o en inp, Problems.CoreutilsLite.Admissible o snap en inp

/-! ## Programs judged by their container events -/

/-- **A postcondition on container events**: every LPS event is supported by the adapter, and
the execution halts, unkilled, with a status `k` such that `G` holds of the container events
(after the events `pre` already read) and `k`. -/
def EvPost {o : Oracle} (G : List Ev → Word → Prop) (pre : List Ev) : Omni.Post (isaOf o) :=
  fun tr out => ∃ es, mapEvs tr = some es ∧ ∃ final, out = .halt final ∧
    final.model.killedBy = none ∧ ∃ k, final.model.halted = some k ∧ G (pre ++ es) k

/-- **The hypotheses of the general run theorem**, under a system call table `sp`: every
admissible launch of `snap` has only finite, error-free LPS executions meeting `EvPost G []`; no
reachable configuration is about to create a task; and some launch is admissible. -/
structure Sound (sp : Sys SyscallEffect) (snap : X86Launch.Snapshot)
    (G : List Ev → Word → Prop) : Prop where
  exec : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    Omni.Exec snap.image.segments sp noFilter (X86Launch.init (isaOf o) snap en limit inp)
      (EvPost G [])
  noClone : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    NoCloneFromWith sp snap.image.segments (X86Launch.init (isaOf o) snap en limit inp)
  launch : ∃ o en inp, Problems.CoreutilsLite.Admissible o snap en inp

/-! ## Programs that write a bounded output -/

/-- **Bounded output**: every LPS event is supported by the adapter, the container events read off
them (`mapEvs`), after the events `pre` already read, are a prefix of `w`, and the execution halts
with status `k` and no kill. `PrefixPost w k []` is the postcondition of `Emits`. -/
def PrefixPost {o : Oracle} (w : List Ev) (k : Word) (pre : List Ev) : Omni.Post (isaOf o) :=
  fun tr out => (∃ es, mapEvs tr = some es ∧ pre ++ es <+: w) ∧
    ∃ final, out = .halt final ∧ final.model.killedBy = none ∧ final.model.halted = some k

/-- The hypotheses for programs with output: every admissible launch of `snap` has only finite,
error-free LPS executions whose container events are a prefix of `w` (only outputs) and which halt
with status `k`; no reachable configuration is about to create a task; and some launch is
admissible. `ExitOnly snap k` is the case `w = []` (`ExitOnly.emits`). -/
structure Emits (snap : X86Launch.Snapshot) (k : Word) (w : List Ev) : Prop where
  exec : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    Omni.Exec snap.image.segments Probes.spec noFilter (X86Launch.init (isaOf o) snap en limit inp)
      (PrefixPost w k [])
  noClone : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    NoCloneFrom snap.image.segments (X86Launch.init (isaOf o) snap en limit inp)
  launch : ∃ o en inp, Problems.CoreutilsLite.Admissible o snap en inp
  outputs : ∀ e ∈ w, e.isInput = false

/-- **Execution with clone freedom** under the table `sp`: every execution meets `post`, and no reachable configuration is about to create a task. -/
def ExecN (segs : List Segment) (sp : Sys SyscallEffect) {isa : UserIsa}
    (c : Silmaril.Process.LPS.Config isa) (post : Omni.Post isa) : Prop :=
  Omni.Exec segs sp noFilter c post ∧ NoCloneFromWith sp segs c

/-- A flag-oracle configuration over the memory `mem` (`Probe.ocfg` is the one over the initial
memory). -/
abbrev ocfgM (o : Oracle) (core : Silmaril.X86.State) (mem : Silmaril.Process.Memory)
    (pending : Option Word) (counter : Nat) (model : Silmaril.Process.LPS.Model) :
    Silmaril.Process.LPS.Config (isaOf o) :=
  ⟨⟨⟨⟨core, mem⟩, pending⟩, counter⟩, model⟩

/-! ## Loading ELF contents -/

/-- An ELF file as LPS's loader reads it. -/
def elfBytes (bs : List UInt8) : Silmaril.Formats.ELF.Bytes := (bs.map UInt8.toBitVec).toArray

/-- **The ELF loader of the adapter**: LPS's x86-64 loader (fixed-address `ET_EXEC`, no
interpreter), at the native machine; its acceptance does not depend on the flag oracle. -/
def loadElf (bs : List UInt8) : Option X86Launch.Snapshot :=
  ELFImage.loadX86 x86ExtNative (elfBytes bs)

/-- **The machine runtime over ELF images**: the program is the ELF file at the entry point
(`ShapeKind.static`), loaded by `loadElf`, run by `lps` under `seqPolicy`. -/
def runtime : MachRuntime (Flat (List UInt8)) X86Launch.Snapshot Ev where
  load img := match (Shape.entry .static loadElf).program img with
    | some p => .ok p
    | none => .error .noShape
  machine := lps

/-- **The machine runtime over OCI images**: read the image (`Oci.load`, with checked digests,
refusing anything outside its profile), then the ELF file at its entry point, run by `lps`
under `seqPolicy`. -/
def ociRuntime : MachRuntime (Oci.Layout × Oci.Digest) X86Launch.Snapshot Ev where
  load i := (Oci.load i.1 i.2).bind runtime.load
  machine := lps

end Silmaril.Containers.Lps
