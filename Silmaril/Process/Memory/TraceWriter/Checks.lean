module

import Silmaril.Semantics.ReadWrite.Writer.Thms
import Silmaril.Semantics.Page.Trace.Thms
import Silmaril.Process.Memory.Trace.Thms

open Silmaril.Semantics Silmaril.Semantics.ReadWrite

namespace ReadWriteWriterChecks

section Page

private def pageProgram : Page.Program (Fin 2) Nat (Nat × Nat) :=
  Page.Program.write 0 11 >>= fun _ =>
    Page.Program.read 0 >>= fun first =>
      Page.Program.read 1 >>= fun second => pure (first, second)

private def pageWrite : Trace (Fin 2) Nat := [.write 0 11]
private def pageReads : Trace (Fin 2) Nat := [.read 0 11, .read 1 7]
private def pageTrace : Trace (Fin 2) Nat := pageWrite ++ pageReads

private def pageObservation : ValueWriter (Fin 2) Nat (Nat × Nat) := do
  pageWrite.record ()
  pageReads.record (11, 7)

example : pageProgram.Records pageTrace (11, 7) :=
  .write (.read (.read .pure))

private def pageInitial : Page.MapMemory (Fin 2) Nat := fun page =>
  if page = 0 then .undef else .defined 7

example : pageTrace.run (Page.mapStore (Fin 2) Nat).access pageInitial =
    some (Page.override pageInitial 0 (.defined 11)) := rfl

example : pageObservation = pageTrace.record (11, 7) := rfl

example : (WriterLog.mapLog ValueLog.eraseValues pageObservation).run =
    ((11, 7), FreeMonoid.ofList [.write 0, .read 0, .read 1]) := rfl

example : (WriterLog.mapLog ValueLog.reads pageObservation).run =
    ((11, 7), FreeMonoid.ofList [(0, 11), (1, 7)]) := rfl

example :
    let sets := (WriterLog.mapLog ValueLog.accessSets pageObservation).run.2
    let summary := (WriterLog.mapLog ValueLog.useDef pageObservation).run.2
    0 ∈ sets.reads ∧ 0 ∉ summary.uses ∧ 1 ∈ summary.uses ∧ 0 ∈ summary.defs := by
  change 0 ∈ (ValueLog.accessSets pageTrace.toLog).reads ∧
    0 ∉ (ValueLog.useDef pageTrace.toLog).uses ∧
    1 ∈ (ValueLog.useDef pageTrace.toLog).uses ∧ 0 ∈ (ValueLog.useDef pageTrace.toLog).defs
  simp only [ValueLog.accessSets_toLog, ValueLog.useDef_toLog, Trace.mem_accessSets_reads,
    Trace.mem_useDef_uses, Trace.mem_useDef_defs]
  exact ⟨⟨11, List.mem_cons_self⟩, fun used => used.1 rfl,
    ⟨by decide, Or.inr (Or.inl rfl)⟩, ⟨11, List.mem_cons_self⟩⟩

end Page

section Byte

open Silmaril.Process

private def byteInitial : Memory :=
  ⟨[⟨16, 1, ⟨true, true, false⟩⟩], Memory.install ∅ 16 [0x11]⟩

private def byteFinal : Memory :=
  { byteInitial with bytes := Memory.install byteInitial.bytes 16 [0x42] }

private def byteTrace : Trace Nat Byte := [.write 16 0x42, .read 16 0x42]

private theorem byteReplay : byteTrace.Replays Memory.byteAccess byteInitial byteFinal := by
  have get : byteFinal.bytes.get? 16 = some 0x42 :=
    Memory.install_get byteInitial.bytes 16 [0x42] 0 (by decide)
  refine ⟨byteFinal, rfl, ?_, rfl⟩
  unfold Memory.byteAccess Memory.readBytes Memory.readWith
  simp only [show byteFinal.checkSpan .read 16 1 = true from rfl, ite_true, Memory.readBacking, get]
  rfl

private def byteObservation : WriterT (ValueLog Nat Byte) Option Memory :=
  WriterT.mk ((byteTrace.run Memory.byteAccess byteInitial).map fun final => (final, byteTrace.toLog))

example : (WriterLog.mapLog ValueLog.eraseValues byteObservation).run =
    some (byteFinal, FreeMonoid.ofList [.write 16, .read 16]) := by
  have run : byteTrace.run Memory.byteAccess byteInitial = some byteFinal :=
    Trace.run_eq_some_iff.mpr byteReplay
  change Prod.map id ValueLog.eraseValues <$>
    ((byteTrace.run Memory.byteAccess byteInitial).map fun final => (final, byteTrace.toLog)) = _
  rw [run]
  rfl

example : Cslib.IsMonadHom (WriterT (ValueLog Nat Byte) Option)
    (WriterT (UseDef Nat) Option) (WriterLog.mapLog ValueLog.useDef) :=
  WriterLog.isMonadHom ValueLog.useDef

example :
    WriterLog.mapLog AddressLog.writes (WriterLog.mapLog ValueLog.eraseValues byteObservation) =
      WriterLog.mapLog EntryLog.eraseValues (WriterLog.mapLog ValueLog.writes byteObservation) :=
  WriterLog.mapLog_eraseValues_writes byteObservation

end Byte

end ReadWriteWriterChecks
