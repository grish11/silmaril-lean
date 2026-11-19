module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Initialization.Defs
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Bounded candidate obligation. Fixed distinct ELF/global/GOT and
caller-storage addresses, arbitrary caller payload. This post-loader context
selects the actual non-interposed global binding. Neither dynamic-loader
correctness nor whole-TU/global-startup adequacy follows from it. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteGlobalVersion.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual
abbrev Input := Initialization.Payload
abbrev Observation := Option Int × Prop
def placement : Silmaril.Project.Shapes.Placement := ⟨functionAddress, functionCode, 0⟩
/-- Restore ONLY the driver diagnostic field; all actual memory fields remain. -/
def memoryUnchanged (before after : Mem.Concrete.State) : Prop :=
  {after with currentLocation := before.currentLocation} = before
def returnedAddress : Val → Option Int
  | .loaded (.specified (.pointer (.allocated id address))) =>
      if id == 1 then some address else none
  | _ => none
def context : Context Input Observation where
  sourceEntry input state := Initialization.prepare input = .ok state
  machineEntry _ machine :=
    SysV.CallEntry placement Source.signature 0 .nil machine ∧
    Initialization.unrelatedAddress + 65536 < (machine.core.read .rsp).toNat ∧
    machine.memory.Permitted .read globalAddress 7 ∧
    machine.memory.Permitted .read gotAddress 8 ∧
    machine.memory.Permitted .read Initialization.unrelatedAddress 64
  related input _ machine :=
    Silmaril.X86.Ext.loadN machine.memory gotAddress 8 = some (BitVec.ofNat 64 globalAddress) ∧
    (∀ j : Fin 7, machine.memory.bytes.get? (globalAddress+j.val) = globalBytes[j.val]?) ∧
    (∀ j : Fin 64, machine.memory.bytes.get? (Initialization.unrelatedAddress+j.val) = some (input j))
  footprint _ machine := SysV.StackBelow machine 0
  sourceObservation _ before after value :=
    (returnedAddress value, memoryUnchanged before.memory after.memory)
  machineObservation _ _ after := (some ((after.core.read .rax).toNat : Int), True)
  callees := []
/-- Joint entry for every payload, source safety, actual first returns, ABI,
zero private frame, all unrelated machine bytes/mappings and complete source
memory preservation are demanded; no desired result is an entry premise.
The registered proposition remains unproved. -/
def statement : Prop :=
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F functionAddress functionCode ∧
  Silmaril.Elf.Staged.Reader.PartIs Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F
    [⟨972146, 7⟩] (Silmaril.Elf.Link.DynElf.Rd.read 972146 7 .pure) 54074514157107 ∧
  Silmaril.Elf.Staged.Reader.PartIs Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F
    [⟨53296, 24⟩] (Silmaril.Elf.Link.DynElf.Rd.read 53296 24 .pure) 18460161865934271123737998847944 ∧
  C.ElaboratesWith Source.inputs Source.ail "sqlite3_libversion" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context

@[problem "silmaril.corpus.sqlite.libversion.global-pointer.contextual"
  (title := "Actual SQLite global version pointer with restricted resolved GOT binding")]
def Task.compilesTo : Prop := statement
end Silmaril.Elf.Corpus.SqliteGlobalVersion.Context
