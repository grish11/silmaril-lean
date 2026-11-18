module

public import Silmaril.Containers.Lps.Defs
public import Silmaril.Containers.Machine.Thms
public import Silmaril.Process.LPS.Probes.Oracle
import Silmaril.Proofs.Containers.Lps.Basic

/-!
# The LPS adapter: theorems

PROVED (standard axioms). Proofs are in `Silmaril.Proofs.Containers.Lps`.

**Programs that only exit.** For a snapshot that satisfies `ExitOnly snap k` (every admissible
launch, for every flag oracle and allocation limit, has only finite, error-free LPS executions
whose events are stop events and which halt with status `k`; no reachable configuration is
about to create a task; and some launch is admissible):

* `runs_eq`: every run of the adapter under `seqPolicy` is `done [] (exited (k mod 256))`;
* `run_exists`: that run exists, so the statement is not vacuous.

The proof follows the adapter step by step: from a configuration satisfying the invariant every
adapter step is an internal LPS step (no events to emit, no unsupported event, no error, no task
creation), adapter paths are finite (an infinite one would be an infinite LPS execution, which
`Omni.Exec` excludes), and no state is stuck (`Omni.Exec` has a step at every running
configuration). Clone freedom is a separate hypothesis because `Omni.Exec` constrains traces and
outcomes, not intermediate states, and LPS models `fork` as a successful step.

**Clone freedom along a probe's execution.** `noClone_instr`, `noClone_trap`, `noClone_exit`
mirror the probe kit's execution rules (`Probes.Probe.oexec_*`) with the same side conditions,
so a probe's unique-successor chain proves `NoCloneFrom` with the same tactic script
(`noclone_instr`, `noclone_trap`, `noclone_exit`).
-/

public section

namespace Silmaril.Containers.Lps

open Silmaril.Containers Silmaril.Containers.Mach
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem runs_eq {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) (b : Beh Ev)
    (hb : lps.Run seqPolicy snap b) : b = .done [] (.exited (k.toNat % 256).toUInt8) :=
  Silmaril.Proofs.Containers.Lps.runs_eq h b hb

theorem run_exists {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) :
    lps.Run seqPolicy snap (.done [] (.exited (k.toNat % 256).toUInt8)) :=
  Silmaril.Proofs.Containers.Lps.run_exists h

theorem noClone_instr (P : Probe) (oracle : Oracle) [Probe.Checked P] {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : NoCloneFrom P.segs (P.ocfg oracle core' none counter model)) :
    NoCloneFrom P.segs (P.ocfg oracle core none counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_instr P oracle running lazy rip fits two notSyscall
    decoded exec rest

theorem noClone_trap (P : Probe) (oracle : Oracle) [Probe.Checked P] {off : Nat}
    {core : Silmaril.X86.State} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : NoCloneFrom P.segs (P.ocfg oracle (Probe.complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model)) :
    NoCloneFrom P.segs (P.ocfg oracle core none counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_trap P oracle running lazy rip two isSyscall rest

theorem noClone_exit (P : Probe) (oracle : Oracle) {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} (number : n = 60)
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false) :
    NoCloneFrom P.segs (P.ocfg oracle core (some n) counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_exit P oracle number running clear

macro "noclone_instr " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic|
    (apply Silmaril.Containers.Lps.noClone_instr _ _ (off := $off) (len := $len) (instruction := $instr)
      <;> oprobe_sides))

macro "noclone_trap " off:term:max : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.noClone_trap _ _ (off := $off) <;> oprobe_sides))

macro "noclone_exit" : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.noClone_exit <;> oprobe_sides))

end Silmaril.Containers.Lps
