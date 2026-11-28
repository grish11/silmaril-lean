module

import Silmaril.Process.Memory.Trace.Projections.Thms
import Silmaril.Semantics.Page.Trace.Thms
import Silmaril.Semantics.ReadWrite.Labelled.Thms
import Silmaril.Semantics.ReadWrite.Writer.State.Thms

open Silmaril.Semantics Silmaril.Semantics.ReadWrite

namespace ReadWriteIntegrationChecks

variable {Value State Ignored : Type}

open LoggedState (run mapLog)

universe u

-- The write to first changes its next read and intervenes between equal reads of second.
private def sample {m : Type → Type u} [Bind m] [Pure m] (load : Nat → m Value)
    (store : Nat → Value → m Ignored) (first second : Nat) (newFirst newSecond : Value) :
    m (Value × Value × Value × Value) := do
  let old ← load first
  let _ ← store second newSecond
  let before ← load second
  let _ ← store first newFirst
  let updated ← load first
  let after ← load second
  pure (old, before, updated, after)

private def program (first second : Nat) (newFirst newSecond : Value) :
    Program Nat Value (Value × Value × Value × Value) :=
  sample Program.read Program.write first second newFirst newSecond

private def sampleTrace (first second : Nat) (old newFirst newSecond : Value) : Trace Nat Value :=
  [.read first old, .write second newSecond, .read second newSecond,
    .write first newFirst, .read first newFirst, .read second newSecond]

private theorem sampleViews {p : LoggedState State (ValueLog Nat Value) (Value × Value × Value × Value)}
    {initial final : State} {first second : Nat}
    {old newFirst newSecond : Value}
    (success : run p initial =
      some (((old, newSecond, newFirst, newSecond), final),
        (sampleTrace first second old newFirst newSecond).toLog)) :
    let output := ((old, newSecond, newFirst, newSecond), final)
    let both : Set Nat := {address | address = first ∨ address = second}
    run (mapLog ValueLog.eraseValues p) initial =
      some (output, FreeMonoid.ofList
        [.read first, .write second, .read second, .write first, .read first, .read second]) ∧
    run (mapLog ValueLog.reads p) initial =
      some (output, FreeMonoid.ofList
        [(first, old), (second, newSecond), (first, newFirst), (second, newSecond)]) ∧
    run (mapLog ValueLog.writes p) initial =
      some (output, FreeMonoid.ofList [(second, newSecond), (first, newFirst)]) ∧
    run (mapLog ValueLog.accessSets p) initial = some (output, ⟨both, both⟩) ∧
    run (mapLog ValueLog.useDef p) initial = some (output, ⟨{first}, both⟩) := by
  simp only [LoggedState.run_mapLog, success, Option.map_some, Prod.map_apply, id_eq,
    ValueLog.accessSets_toLog, ValueLog.useDef_toLog]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · congr 2
    apply AccessSets.ext <;> apply Set.ext <;> intro address
    · simp [Trace.Reads, sampleTrace, Trace.reads, List.filterMap, exists_or, or_left_comm]
    · change (sampleTrace first second old newFirst newSecond).Defs address ↔
        address = first ∨ address = second
      simp [Trace.Defs, sampleTrace, Trace.writes, List.filterMap, exists_or, or_comm]
  · congr 2
    apply UseDef.ext <;> apply Set.ext <;> intro address
    · change (sampleTrace first second old newFirst newSecond).Uses address ↔ address = first
      by_cases h : address = second <;> simp [sampleTrace, Trace.Uses, h]
    · simp [Trace.Defs, sampleTrace, Trace.writes, List.filterMap, exists_or, or_comm]

section Byte

open Silmaril.Process

private def byteInitial : Memory :=
  ⟨[⟨16, 2, ⟨true, true, false⟩⟩], Memory.install ∅ 16 [0x11]⟩

private def byteMiddle : Memory :=
  { byteInitial with bytes := Memory.install byteInitial.bytes 17 [0x33] }

private def byteFinal : Memory :=
  { byteMiddle with bytes := Memory.install byteMiddle.bytes 16 [0x42] }

private def byteTrace : Trace Nat Byte := sampleTrace 16 17 0x11 0x42 0x33

private def byteProgram : Program Nat Byte (Byte × Byte × Byte × Byte) :=
  program 16 17 0x42 0x33

private theorem byteFirst : Memory.byteAccess.read byteInitial 16 = some 0x11 :=
  Memory.byteAccess_read_iff.mpr ⟨rfl, Memory.install_get ∅ 16 [0x11] 0 (by decide)⟩

private theorem byteSecond : Memory.byteAccess.read byteMiddle 17 = some 0x33 :=
  Memory.byteAccess_read_iff.mpr ⟨rfl, Memory.install_get byteInitial.bytes 17 [0x33] 0 (by decide)⟩

private theorem byteUpdated : Memory.byteAccess.read byteFinal 16 = some 0x42 :=
  Memory.byteAccess_read_iff.mpr ⟨rfl, Memory.install_get byteMiddle.bytes 16 [0x42] 0 (by decide)⟩

private theorem byteWriteSecond : Memory.byteAccess.write byteInitial 17 0x33 = some byteMiddle := rfl
private theorem byteWriteFirst : Memory.byteAccess.write byteMiddle 16 0x42 = some byteFinal := rfl

private theorem byteSecondAfter : Memory.byteAccess.read byteFinal 17 = some 0x33 :=
  (Memory.byteAccess_frames byteWriteFirst (by decide)).trans byteSecond

private theorem byteRun : run (byteProgram.interpret Memory.byteAccess) byteInitial =
    some (((0x11, 0x33, 0x42, 0x33), byteFinal), byteTrace.toLog) := by
  simp only [byteProgram, program, sample, Program.interpret, Program.read, Program.write,
    Cslib.FreeM.liftM_bind, Cslib.FreeM.liftM_lift, Cslib.FreeM.liftM_pure,
    LoggedState.run_bind, LoggedState.run_pure, Access.run_logOp_read, Access.run_logOp_write,
    Option.map, Option.bind,
    byteFirst, byteWriteSecond, byteSecond, byteWriteFirst, byteUpdated, byteSecondAfter]
  rfl

example := sampleViews byteRun

private theorem byteReplay : byteTrace.Replays Memory.byteAccess byteInitial byteFinal :=
  Program.replays_of_run byteRun

example : Memory.byteAccess.labelled.Path byteInitial byteTrace byteFinal :=
  Trace.replays_iff_path.mp byteReplay

example : (Memory.writeProjection byteTrace).run byteInitial = some byteFinal :=
  Memory.ByteWriteTrace.run_eq_some_iff.mpr (Memory.writeProjection_replays byteReplay)

example : (Memory.readProjection byteTrace).run byteInitial = none := by
  apply Trace.run_eq_none_iff.mpr
  rintro ⟨_, replay⟩
  have read := (ReadTrace.replays_iff byteTrace.reads).mp replay |>.2 (16, 0x42)
    (by simp [byteTrace, sampleTrace, Trace.reads, List.filterMap])
  rw [byteFirst] at read
  exact (by decide : (0x11 : Byte) ≠ 0x42) (Option.some.inj read)

example : byteTrace.ReadsMatchLastWrite 16 :=
  Memory.replay_readsMatchLastWrite byteReplay 16

example : byteTrace.ChangedReadAddresses 16 := by
  refine ⟨0x11, [.write 17 0x33, .read 17 0x33, .write 16 0x42], 0x42,
    ⟨[], [.read 17 0x33], rfl, ?_⟩, by decide⟩
  simp [Trace.Reads, Trace.reads, List.filterMap]

example :
    let gap : Trace Nat Byte := [.write 16 0x42, .read 16 0x42]
    byteTrace.StableWithoutWritesAddresses 17 ∧ ¬ gap.Defs 17 := by
  intro gap
  have pair : byteTrace.ConsecutiveReads 17 0x33 gap 0x33 :=
    ⟨[.read 16 0x11, .write 17 0x33], [], rfl, by simp [gap, Trace.Reads, Trace.reads, List.filterMap]⟩
  exact ⟨⟨⟨0x33, gap, 0x33, pair⟩, byteReplay.stableWithoutWrites Memory.byteAccess_frames⟩,
    by simp [gap, Trace.Defs, Trace.writes, List.filterMap]⟩

-- Address 18 is unmapped. The first read succeeds before the write is rejected.
example : run (mapLog ValueLog.useDef
    (Program.interpret (program 16 18 0x42 0x33) Memory.byteAccess)) byteInitial = none := by
  have rejected : Memory.byteAccess.write byteInitial 18 0x33 = none := rfl
  simp only [LoggedState.run_mapLog, program, sample, Program.interpret, Program.read, Program.write,
    Cslib.FreeM.liftM_bind, Cslib.FreeM.liftM_lift,
    LoggedState.run_bind, Access.run_logOp_read, Access.run_logOp_write,
    Option.map, Option.bind, byteFirst, rejected]

end Byte

section Page

private def pageModel : Page.Model Nat Nat (Page.MapMemory Nat Nat) :=
  ⟨Page.mapStore Nat Nat, fun _ _ => False⟩

private def pageInitial : Page.MapMemory Nat Nat
  | 0 => .defined 1
  | 1 => .undef
  | _ => .absent

private def pageFinal := Page.override (Page.override pageInitial 1 (.defined 7)) 0 (.defined 2)
private def pageTrace : Trace Nat Nat := sampleTrace 0 1 1 2 7
private def pageProgram := sample Page.Program.read Page.Program.write 0 1 2 7
private def pageAccessProgram : Program Nat Nat (Nat × Nat × Nat × Nat) :=
  program 0 1 2 7

private theorem pageRun : run (pageAccessProgram.interpret pageModel.store.access) pageInitial =
    some (((1, 7, 2, 7), pageFinal), pageTrace.toLog) := rfl

example := sampleViews pageRun

example :
    let perOperation := pageAccessProgram.liftM fun op =>
      mapLog ValueLog.useDef (pageModel.store.access.logOp op)
    (run perOperation pageInitial).map Prod.fst = some ((1, 7, 2, 7), pageFinal) := by
  dsimp only
  rw [← Program.mapLog_interpret, LoggedState.run_mapLog_outcome, pageRun]
  rfl

private theorem pageReplay : pageTrace.Replays pageModel.store.access pageInitial pageFinal :=
  Program.replays_of_run pageRun

example : Page.Run pageModel pageProgram pageInitial [.write 1 7, .write 0 2]
    (.returned (1, 7, 2, 7) pageFinal) :=
  (show pageProgram.Records pageTrace (1, 7, 2, 7) from
    .read (.write (.read (.write (.read (.read .pure)))))).run pageReplay

example : pageTrace.writes.toTrace.run pageModel.store.access pageInitial = some pageFinal := rfl
example : pageTrace.reads.toTrace.run pageModel.store.access pageInitial = none := rfl

-- The first read succeeds, but writing to an absent page rejects the whole observation.
example : run (mapLog ValueLog.eraseValues
    (Program.interpret (program 0 2 2 7) pageModel.store.access)) pageInitial = none := rfl

end Page

end ReadWriteIntegrationChecks
