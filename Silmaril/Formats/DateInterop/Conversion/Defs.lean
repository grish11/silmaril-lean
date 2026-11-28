module

public import Silmaril.Formats.DateInterop.Defs

/-! # Exact conversion between signed Date32 days and Date64 milliseconds -/

@[expose] public section

namespace Silmaril.Formats.DateInterop

/-- Scale a signed Date32 day in unbounded integers before constructing Date64.
The scaled value fits signed Int64 throughout the Date32 domain. -/
def Date32.widen (value : Date32.Payload) : Date64.Payload :=
  Int64.ofInt (Date32.toEpochDay value * Date64.millisecondsPerDay)

/-- Check exact whole days and the signed Int32 range before returning a Date32 word. -/
def Date64.narrow? (value : Date64.Payload) : Option Date32.Payload :=
  (Date64.toEpochDay? value).bind Date32.ofEpochDay?

end Silmaril.Formats.DateInterop
