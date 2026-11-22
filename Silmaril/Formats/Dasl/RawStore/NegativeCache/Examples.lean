module

import Silmaril.Formats.Dasl.RawStore.NegativeCache.Thms

namespace Silmaril.Formats.Dasl.RawStore

open Silmaril.Semantics.Naming NegativeCache

private def goodWire : ByteArray := ⟨#[0xF6]⟩
private def badWire : ByteArray := ByteArray.empty

private def singleton (name : Wire.Cid) (wire : ByteArray) : Wire.Cid → Option ByteArray :=
  fun query => if query = name then some wire else none

private def snapshot (name : Wire.Cid) (wire : ByteArray) : Source (nameGraph fun (_ : ByteArray) => some name) where
  bindings := graph (singleton name wire)
  bound := graph_binding _
  compatible := by
    intro query _ hit
    by_cases same : query = name
    · cases same; rfl
    · simp [graph, singleton, same] at hit

private def hit (name : Wire.Cid) (wire : ByteArray) : Verified (snapshot name wire) name :=
  ⟨wire, by simp [snapshot, graph, singleton]⟩

private def loose := objectProfile some
private def strict := objectProfile (Node := Shallow Wire.Cid) fun _ => none

example (name : Wire.Cid) (object : Wire.IsObjectCid name) :
    let cache : Cache (snapshot name badWire) loose := Cache.empty
    let result := stepObject cache name (.ok (hit name badWire))
    result.1 = .invalid .wire ∧ result.2.lookup name = some .wire := by
  simp only [stepObject, objectInput_of_object object]
  exact ⟨rfl, Cache.step_invalid_sound rfl⟩

example (name : Wire.Cid) (object : Wire.IsObjectCid name) :
    let cache : Cache (snapshot name goodWire) strict := Cache.empty
    (stepObject cache name (.ok (hit name goodWire))).2.lookup name = some .node := by
  simp only [stepObject, objectInput_of_object object]
  exact Cache.step_invalid_sound rfl

example (name : Wire.Cid) (object : Wire.IsObjectCid name) :
    let cache : Cache (snapshot name goodWire) loose := Cache.empty
    stepObject cache name (.ok (hit name goodWire)) = (.found .null, cache) := by
  simp only [stepObject, objectInput_of_object object]
  exact Cache.step_found _ rfl

example (name : Wire.Cid) (otherCodec : ¬ Wire.IsObjectCid name) (issue : Deferred) :
    let cache : Cache (snapshot name badWire) loose := Cache.empty
    Wire.readObject (singleton name badWire) name = .invalidWire ∧
      stepObject cache name (.ok (hit name badWire)) = (.deferred .mismatch, cache) ∧
      cache.step name (.error issue) = (.deferred issue, cache) := by
  simp only [stepObject, objectInput_of_mismatch otherCodec]
  exact ⟨readObject_invalidWire_iff.mpr (.inl otherCodec), rfl, rfl⟩

example (name : Wire.Cid) (object : Wire.IsObjectCid name) (extended : Blocks Wire.Cid) :
    ¬ Completes daslDecoder (nameGraph fun _ => some name) (snapshot name badWire).bindings extended name := by
  have bad : Wire.readObject (singleton name badWire) name = .invalidWire :=
    readObject_invalidWire_iff.mpr (.inr ⟨badWire, (hit name badWire).property, rfl⟩)
  obtain ⟨entry, why⟩ := readObject_wire_certificate (source := snapshot name badWire) some
    (fun _ _ found => found) object bad
  exact no_completion_of_wire_certificate entry why

end Silmaril.Formats.Dasl.RawStore
