module

public import Silmaril.Crypto.SHA256
public import Silmaril.Formats.Dasl.Mst.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Mst.Atproto

variable {Name : Type}

def leadingZeroBits : List UInt8 → Nat
  | [] => 0
  | byte :: rest => if byte = 0 then 8 + leadingZeroBits rest else 8 - (byte.toNat.log2 + 1)

/-- Count leading zero two-bit groups in the binary SHA-256 digest. -/
def keyLayer (key : Key) : Nat := leadingZeroBits (Crypto.SHA256.digest key) / 2

def readAt (ctx : Context) : Wire.ReadResult (Shallow Name) → Read Name (ctx.Valid keyLayer) :=
  Mst.readAt keyLayer ctx

def readRoot : Wire.ReadResult (Shallow Name) → Read Name (fun node => (node.rootContext keyLayer).Valid keyLayer node) :=
  Mst.readRoot keyLayer

end Silmaril.Formats.Dasl.Mst.Atproto
