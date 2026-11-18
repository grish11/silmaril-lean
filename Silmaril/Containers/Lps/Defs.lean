module

public import Silmaril.Containers.Machine.Defs
public import Silmaril.Process.LPS.Problems.CoreutilsLite.Spec
public import Silmaril.Process.LPS.ELFImageX86
public import Silmaril.Containers.Oci.Defs

/-!
# The Linux process semantics as a container machine (restricted, sequential)

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
  written on channels 1 and 2 are `Ev.stdout` and `Ev.stderr`, and an exit or kill event is
  dropped (it is the run's stop). **Any other event** (a file, a socket, another channel) is
  outside this restricted adapter: the run ends in `undefined unmodeled`, a statement that the
  adapter makes no claim, never a silent success.
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
three standard channels.

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

/-- The container event of an LPS event: `some evs` for the standard channels and the stop
events (which are dropped), `none` for anything else. -/
def mapEv : Event → Option (List Ev)
  | .readEv ch b => if ch = 0 then some [.stdin [UInt8.ofBitVec b]] else none
  | .writeEv ch b =>
    if ch = 1 then some [.stdout [UInt8.ofBitVec b]]
    else if ch = 2 then some [.stderr [UInt8.ofBitVec b]] else none
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
abbrev LStep (s : St) (evs : List Event) (t : StepTo (isaOf s.oracle)) : Prop :=
  SStep s.segs Probes.spec noFilter s.cfg evs t

/-- **The steps of the adapter.** -/
inductive Step : St → Act Ev → St → Prop where
  /-- Emit a pending event. -/
  | emit {s : St} {e : Ev} {rest : List Ev} (h : s.pending = e :: rest) :
      Step s (.ev e) { s with pending := rest }
  /-- An LPS step whose events are supported. -/
  | lps {s : St} {evs : List Event} {c' : Silmaril.Process.LPS.Config (isaOf s.oracle)} {es : List Ev}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep s evs (.next c')) (hm : mapEvs evs = some es) :
      Step s .tau { s with cfg := c', pending := es }
  /-- An LPS step with an event outside the adapter: no claim. -/
  | unsupported {s : St} {evs : List Event} {c' : Silmaril.Process.LPS.Config (isaOf s.oracle)}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep s evs (.next c')) (hm : mapEvs evs = none) :
      Step s .tau { s with bad := some .unmodeled }
  /-- An LPS error at an unmodelled instruction or system call. -/
  | unmodeled {s : St} {evs : List Event}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep s evs .error) (hu : UnmodeledAt s.segs Probes.spec s.cfg) :
      Step s .tau { s with bad := some .unmodeled }
  /-- Any other LPS error (a fault). -/
  | fault {s : St} {evs : List Event}
      (hp : s.pending = []) (hb : s.bad = none) (hc : ¬ ClonePending s.cfg)
      (h : LStep s evs .error) (hu : ¬ UnmodeledAt s.segs Probes.spec s.cfg) :
      Step s .tau { s with bad := some .memory }
  /-- A task-creation request: the clone policy decides. -/
  | clone {s : St} {x8 : Word} {r : CloneReq}
      (hp : s.pending = []) (hb : s.bad = none) (hh : s.cfg.model.halted = none)
      (hx : (isaOf s.oracle).svcPending s.cfg.ms = some x8) (hn : cloneNumber x8 = true)
      (hr : cloneReq (isaOf s.oracle) s.segs s.cfg.ms x8 = some r) :
      Step s (.clone r) s

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

/-- **The adapter**: LPS for a loaded x86-64 snapshot, as a container machine. -/
abbrev lps : MachineSem X86Launch.Snapshot Ev where
  State := St
  isIn := Ev.isInput
  load snap s := ∃ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp ∧
    s = St.init snap o limit en inp
  step := Step
  final := Final

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

/-- No reachable configuration is about to create a task. -/
def NoCloneFrom {isa : UserIsa} (segs : List Segment) (c : Silmaril.Process.LPS.Config isa) : Prop :=
  ∀ tr c', Star segs Probes.spec noFilter c tr c' → ¬ ClonePending c'

/-- The hypotheses: every admissible launch of `snap` only exits, with status `k`, and never
reaches a task-creation request. -/
structure ExitOnly (snap : X86Launch.Snapshot) (k : Word) : Prop where
  exec : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    Omni.Exec snap.image.segments Probes.spec noFilter (X86Launch.init (isaOf o) snap en limit inp)
      (Post k)
  noClone : ∀ o limit en inp, Problems.CoreutilsLite.Admissible o snap en inp →
    NoCloneFrom snap.image.segments (X86Launch.init (isaOf o) snap en limit inp)
  launch : ∃ o en inp, Problems.CoreutilsLite.Admissible o snap en inp

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
