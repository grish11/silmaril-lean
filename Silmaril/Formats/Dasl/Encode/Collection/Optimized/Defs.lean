module

public import Silmaril.Formats.Dasl.Encode.Collection.Defs
public import Silmaril.Formats.Dasl.SparseRangeSet.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode

/-- The existing maximal signed range layout, exposed over the same finite set
as the generic array layout. This codec does not change the wire profile. -/
def signedRangeSet {Name : Type} : TotalCodec (Finset Int64) (Shallow Name) :=
  SparseRangeSet.codec.viaEquiv SparseRangeSet.equiv.symm

end Silmaril.Formats.Dasl.Encode
