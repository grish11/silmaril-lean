module

public import Silmaril.Formats.Dasl.RawStore.Defs
public import Silmaril.Semantics.Naming.NegativeCache.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.RawStore

open Silmaril.Semantics.Naming NegativeCache

/-- Canonical DASL wire parsing followed by a deterministic, block-local node check. -/
def objectProfile {Node : Type} (node? : Shallow Wire.Cid → Option Node) : Profile ByteArray (Shallow Wire.Cid) Node :=
  ⟨Wire.parse?, node?⟩

/-- The reader's wrong-codec case is not evidence that bytes are invalid. Gate
the object lane before running the cache classifier. -/
def objectInput {policy : Blocks Wire.Cid} {source : Source policy} {name : Wire.Cid}
    (input : Input source name) : Input source name :=
  if name.val[1]? == some 0x71 then input else .error .mismatch

def stepObject {Node : Type} {node? : Shallow Wire.Cid → Option Node} {policy : Blocks Wire.Cid} {source : Source policy}
    (cache : Cache source (objectProfile node?)) (name : Wire.Cid) (input : Input source name) :
    Outcome Node × Cache source (objectProfile node?) :=
  cache.step name (objectInput input)

end Silmaril.Formats.Dasl.RawStore
