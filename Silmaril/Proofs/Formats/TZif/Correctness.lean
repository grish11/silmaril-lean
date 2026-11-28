module

public import Silmaril.Formats.TZif.Defs
import Silmaril.Numeric.TimeZone.Thms

public section

namespace Silmaril.Proofs.Formats.TZif

open Silmaril.Formats Silmaril.Formats.TZif
open Silmaril.Numeric.Timestamp Silmaril.Numeric.TimeZone

theorem locate_bounds {maxBytes : Nat} {file : Bytes} {layout : Layout}
    (parsed : locate maxBytes file = .ok layout) :
    layout.blockEnd + 2 ≤ file.length ∧ file.length ≤ maxBytes := by
  unfold locate at parsed
  split at parsed
  · contradiction
  · rename_i size
    cases compatibility : Internal.header file 0 with
    | error e => simp [compatibility, bind, Except.bind] at parsed
    | ok first =>
      rcases first with ⟨version, counts⟩
      simp only [compatibility, bind, Except.bind] at parsed
      cases selected : Internal.header file (44 + counts.blockSize 4) with
      | error e => simp [selected] at parsed
      | ok second =>
        rcases second with ⟨version', counts'⟩
        rw [selected] at parsed
        dsimp at parsed
        split at parsed
        · contradiction
        · split at parsed
          · contradiction
          · rename_i full
            cases parsed
            exact ⟨Nat.le_of_not_gt full, Nat.le_of_not_gt size⟩

theorem parse_selected_sequence {maxBytes : Nat} {file : Bytes} {block : Block}
    (parsed : parse maxBytes file = .ok block) :
    locate maxBytes file = .ok block.layout ∧
      (List.range block.layout.selected.times).mapM
        (Internal.transition file block.layout block.types) = .ok block.transitions := by
  unfold parse at parsed
  cases layoutEq : locate maxBytes file with
  | error e => simp [layoutEq, bind, Except.bind] at parsed
  | ok layout =>
    simp only [layoutEq, bind, Except.bind] at parsed
    cases footerEq : Internal.footer file layout with
    | error e => simp [footerEq] at parsed
    | ok footer =>
      rw [footerEq] at parsed
      dsimp at parsed
      split at parsed
      · cases typesEq : (List.range layout.selected.types).mapM
            (Internal.localType file layout
              (Internal.octets file layout.designationStart layout.selected.designations)) with
        | error e => simp [typesEq] at parsed
        | ok types =>
          rw [typesEq] at parsed
          dsimp at parsed
          cases transitionsEq : (List.range layout.selected.times).mapM
              (Internal.transition file layout types.toArray) with
          | error e => simp [transitionsEq] at parsed
          | ok transitions =>
            rw [transitionsEq] at parsed
            dsimp at parsed
            split at parsed
            · cases parsed
              exact ⟨rfl, transitionsEq⟩
            · contradiction
      · contradiction

theorem schedule_reflects {block : Block} {start stop : Ticks .utcInstant .second}
    {schedule : Schedule} (built : block.toSchedule? start stop = some schedule) :
    block.permitsStop stop.ticks = true ∧
      schedule.start = start.denote ∧ schedule.stop = stop.denote ∧
      (∃ initial, block.typeAtStart? start.ticks = some initial ∧ initial.specified = true ∧
        schedule.initial = Offset.ofSeconds initial.offsetSeconds) ∧
      (block.interior start.ticks stop.ticks).all (·.localType.specified) = true ∧
      schedule.transitions = (block.interior start.ticks stop.ticks).map TransitionEntry.toTransition := by
  unfold Block.toSchedule? at built
  split at built
  · rename_i permits
    cases initial : block.typeAtStart? start.ticks with
    | none => simp [initial] at built
    | some kind =>
      rw [initial] at built
      dsimp at built
      split at built
      · rename_i specified
        unfold Schedule.ofTransitions? at built
        split at built
        · cases built
          obtain ⟨initialSpecified, interiorSpecified⟩ := Bool.and_eq_true_iff.mp specified
          exact ⟨permits, rfl, rfl, ⟨kind, rfl, initialSpecified, rfl⟩, interiorSpecified, rfl⟩
        · contradiction
      · contradiction
  · contradiction

theorem schedule_support {block : Block} {start stop : Ticks .utcInstant .second}
    {schedule : Schedule} (built : block.toSchedule? start stop = some schedule) (time : UnixTime) :
    ((Rules.scheduled schedule).toLocal? time).isSome = true ↔
      start.denote.ticks ≤ time.ticks ∧ time.ticks < stop.denote.ticks := by
  obtain ⟨_, left, right, _⟩ := schedule_reflects built
  rw [Rules.toLocal_isSome_iff]
  simp only [Rules.Supports, Schedule.Supports, left, right]

theorem schedule_candidate_in_support {block : Block} {start stop : Ticks .utcInstant .second}
    {schedule : Schedule} (built : block.toSchedule? start stop = some schedule)
    {wall : WallTime} {time : UnixTime} (candidate : time ∈ (Rules.scheduled schedule).candidates wall) :
    start.denote.ticks ≤ time.ticks ∧ time.ticks < stop.denote.ticks := by
  have mapped := Rules.mem_candidates_iff.mp candidate
  apply (schedule_support built time).mp
  simp [Rules.Matches] at mapped
  simp [mapped]

end Silmaril.Proofs.Formats.TZif
