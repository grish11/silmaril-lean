module

public import Silmaril.Formats.Dasl.Mst.Atproto.Defs
import Silmaril.Proofs.Formats.Dasl.MstAtproto

public section

namespace Silmaril.Formats.Dasl.Mst.Atproto

theorem keyLayer_le (key : Key) : keyLayer key ≤ 128 := Proofs.Formats.Dasl.MstAtproto.keyLayer_le key

end Silmaril.Formats.Dasl.Mst.Atproto
