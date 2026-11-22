module

public import Silmaril.Formats.Dasl.RawStore.NegativeCache.Defs
public import Silmaril.Formats.Dasl.RawStore.Thms
public import Silmaril.Semantics.Naming.NegativeCache.Thms

public section

namespace Silmaril.Formats.Dasl.RawStore

open Silmaril.Semantics.Naming NegativeCache

variable {Node : Type} {policy : Blocks Wire.Cid} {source : Source policy} {name : Wire.Cid}

theorem objectInput_of_object (object : Wire.IsObjectCid name) (input : Input source name) : objectInput input = input := by
  simp only [objectInput, Wire.IsObjectCid] at *
  simp [object]

theorem objectInput_of_mismatch (wrong : ¬ Wire.IsObjectCid name) (input : Input source name) :
    objectInput input = .error .mismatch := by
  simp only [objectInput, Wire.IsObjectCid] at *
  simp [wrong]

/-- An `invalidWire` state can be reused only if the request is for an object
and the original read belongs to the compatible, binding snapshot. -/
theorem readObject_wire_certificate (node? : Shallow Wire.Cid → Option Node) {read : Wire.Cid → Option ByteArray}
    (included : Subset (graph read) source.bindings) (object : Wire.IsObjectCid name)
    (bad : Wire.readObject read name = .invalidWire) :
    ∃ entry : Rejection source (objectProfile node?) name, entry.cause = .wire :=
  let ⟨wire, hit, malformed⟩ := (readObject_invalidWire_iff.mp bad).resolve_left (fun wrong => wrong object)
  ⟨⟨⟨wire, included hit⟩, .wire, Profile.wire_rejection_iff.mpr malformed⟩, rfl⟩

/-- Wire rejection (unlike a stricter node-profile rejection) obstructs even
plain DASL completion from this root. -/
theorem no_completion_of_wire_certificate {node? : Shallow Wire.Cid → Option Node}
    (entry : Rejection source (objectProfile node?) name) (wire : entry.cause = .wire)
    {extended : Blocks Wire.Cid} : ¬ Completes daslDecoder policy source.bindings extended name :=
  no_completion_of_malformed_root entry.verified.property (by
    rw [daslDecoder_parse]
    exact Profile.wire_rejection_iff.mp (wire ▸ entry.checked))

end Silmaril.Formats.Dasl.RawStore
