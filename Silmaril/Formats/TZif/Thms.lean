module

public import Silmaril.Formats.TZif.Defs
import Silmaril.Proofs.Formats.TZif.Correctness

/-! # TZif layout and schedule support -/

public section

namespace Silmaril.Formats.TZif

open Numeric.Timestamp Numeric.TimeZone

/-- Both footer delimiters fit after the selected block and the file fits the budget. -/
theorem locate_bounds {maxBytes : Nat} {file : Bytes} {layout : Layout}
    (parsed : locate maxBytes file = .ok layout) :
    layout.blockEnd + 2 ≤ file.length ∧ file.length ≤ maxBytes :=
  Proofs.Formats.TZif.locate_bounds parsed

/-- The returned sequence reads every selected transition in its original wire order. -/
theorem parse_selected_sequence {maxBytes : Nat} {file : Bytes} {block : Block}
    (parsed : parse maxBytes file = .ok block) :
    locate maxBytes file = .ok block.layout ∧
      (List.range block.layout.selected.times).mapM
        (Internal.transition file block.layout block.types) = .ok block.transitions :=
  Proofs.Formats.TZif.parse_selected_sequence parsed

/-- The schedule keeps the selected initial type and all interior transitions in order,
    with exact second offsets and no unspecified local types. -/
theorem schedule_reflects {block : Block} {start stop : Ticks .utcInstant .second}
    {schedule : Schedule} (built : block.toSchedule? start stop = some schedule) :
    block.permitsStop stop.ticks = true ∧
      schedule.start = start.denote ∧ schedule.stop = stop.denote ∧
      (∃ initial, block.typeAtStart? start.ticks = some initial ∧ initial.specified = true ∧
        schedule.initial = Offset.ofSeconds initial.offsetSeconds) ∧
      (block.interior start.ticks stop.ticks).all (·.localType.specified) = true ∧
      schedule.transitions = (block.interior start.ticks stop.ticks).map TransitionEntry.toTransition :=
  Proofs.Formats.TZif.schedule_reflects built

/-- Forward conversion is defined exactly on the requested half-open interval. -/
theorem schedule_support {block : Block} {start stop : Ticks .utcInstant .second}
    {schedule : Schedule} (built : block.toSchedule? start stop = some schedule) (time : UnixTime) :
    ((Rules.scheduled schedule).toLocal? time).isSome = true ↔
      start.denote.ticks ≤ time.ticks ∧ time.ticks < stop.denote.ticks :=
  Proofs.Formats.TZif.schedule_support built time

/-- Every inverse candidate lies in the same interval. -/
theorem schedule_candidate_in_support {block : Block} {start stop : Ticks .utcInstant .second}
    {schedule : Schedule} (built : block.toSchedule? start stop = some schedule)
    {wall : WallTime} {time : UnixTime} (candidate : time ∈ (Rules.scheduled schedule).candidates wall) :
    start.denote.ticks ≤ time.ticks ∧ time.ticks < stop.denote.ticks :=
  Proofs.Formats.TZif.schedule_candidate_in_support built candidate

end Silmaril.Formats.TZif
