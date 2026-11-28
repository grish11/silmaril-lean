module

import Silmaril.Numeric.TimeZone.Named.Defs
meta import Silmaril.Numeric.TimeZone.Named.Defs
meta import Silmaril.Numeric.TimeZone.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Numeric.TimeZone Silmaril.Numeric.Timestamp

private def exampleZone := NamedZone.ofTransitions? "Example/Zone" ⟨0⟩ ⟨30⟩ 0
  [⟨⟨10⟩, 5⟩, ⟨⟨20⟩, 0⟩]

#guard exampleZone.map (·.name) = some "Example/Zone"
#guard (exampleZone.bind fun zone => zone.toLocal? (⟨9999⟩ : Ticks .utcInstant .millisecond)) =
    some ⟨9999000000⟩
#guard (exampleZone.bind fun zone => zone.toLocal? (⟨10⟩ : Ticks .utcInstant .second)) =
    some ⟨15000000000⟩
#guard (exampleZone.bind fun zone => zone.toLocal? (⟨-1⟩ : UnixTime)) = none
#guard (exampleZone.bind fun zone => zone.toLocal? (⟨30⟩ : Ticks .utcInstant .second)) = none
#guard (exampleZone.map fun zone => zone.resolveLocal (⟨10000000⟩ : Ticks .localReading .microsecond)) =
    some .noSolution
#guard (exampleZone.map fun zone => zone.resolveLocal (⟨15000000000⟩ : WallTime)) =
    some (.unique ⟨10000000000⟩)
#guard (exampleZone.map fun zone => zone.resolveLocal (⟨20000000001⟩ : WallTime)) =
    some (.ambiguous ⟨15000000001⟩ ⟨20000000001⟩ [])

private def threefold := NamedZone.ofTransitions? "Example/Triple" ⟨0⟩ ⟨30⟩ 20
  [⟨⟨10⟩, 10⟩, ⟨⟨20⟩, 0⟩]

#guard (threefold.map fun zone => zone.resolveLocal (⟨20⟩ : Ticks .localReading .second)) =
    some (.ambiguous ⟨0⟩ ⟨10000000000⟩ [⟨20000000000⟩])
#guard (NamedZone.ofTransitions? "unordered" ⟨0⟩ ⟨30⟩ 0 [⟨⟨20⟩, 0⟩, ⟨⟨10⟩, 0⟩]).isNone
#guard (NamedZone.ofTransitions? "duplicate" ⟨0⟩ ⟨30⟩ 0 [⟨⟨10⟩, 0⟩, ⟨⟨10⟩, 0⟩]).isNone
#guard (NamedZone.ofTransitions? "outside" ⟨0⟩ ⟨30⟩ 0 [⟨⟨30⟩, 1⟩]).isNone
#guard (NamedZone.ofTransitions? "empty support" ⟨0⟩ ⟨0⟩ 0 []).isNone
