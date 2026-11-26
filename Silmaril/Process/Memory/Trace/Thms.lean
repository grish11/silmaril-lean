module

public import Silmaril.Process.Memory.Trace.Defs
public import Silmaril.Semantics.ReadWrite.Thms
import Silmaril.Proofs.Process.Memory.Trace.Laws

public section
namespace Silmaril.Process.Memory

open Silmaril.Semantics

theorem byteAccess_frames : byteAccess.Frames byteAccess.read :=
  Proofs.Process.Memory.byteAccess_frames

/-- A replay freezes mapping metadata and can change backing bytes only at
addresses in the trace's write set. -/
theorem replay_writesWithin {trace : ReadWrite.Trace Nat Byte} {before after : Memory}
    (run : trace.Replays byteAccess before after) :
    WritesWithin before after trace.Defs :=
  Proofs.Process.Memory.replay_writesWithin run

end Silmaril.Process.Memory
