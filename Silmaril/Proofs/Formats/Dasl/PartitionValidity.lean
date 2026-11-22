module

public import Silmaril.Formats.Dasl.Encode.Partition.Validity.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.PartitionValidity

open Silmaril.Formats.Dasl Encode Encode.Partition Silmaril.Semantics Naming

variable {Name Root Repr : Type} [LinearOrder Name]

theorem decoded_iff (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (read : Root → Option ByteArray) (root : Root) (labels : OrderedMap Name Name) :
    observeNamed profile name read root = .decoded labels ↔ namedMaps profile name (graph read) root labels := by
  unfold observeNamed namedMaps project push graph
  cases guard : profile.objectName root <;> cases hit : read root
  · simp
  · simp
  · simp
  · rename_i bytes
    cases decode : profile.decode? (nameMap name) bytes <;> simp [decode]

theorem unknown_iff (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (read : Root → Option ByteArray) (root : Root) :
    observeNamed profile name read root = .unknown ↔ profile.objectName root = true ∧ read root = none := by
  unfold observeNamed
  cases guard : profile.objectName root <;> cases hit : read root
  · simp
  · simp
  · simp
  · rename_i bytes
    cases decode : profile.decode? (nameMap name) bytes <;> simp [decode]

theorem rejected_extension (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    {read : Root → Option ByteArray} {store : Relation Root ByteArray} {root : Root}
    (incl : Subset (graph read) store) (bound : Binding store)
    (rejected : observeNamed profile name read root = .rejected) (labels : OrderedMap Name Name) :
    ¬ namedMaps profile name store root labels := by
  intro ⟨guard, bytes, stored, decodes⟩
  unfold observeNamed at rejected
  rw [ite_eq_left guard] at rejected
  cases hit : read root with
  | none => simp [hit] at rejected
  | some seen =>
    have equal := bound (incl (show graph read root seen from hit)) stored
    subst seen
    change profile.decode? (nameMap name) bytes = some labels at decodes
    simp [hit, decodes] at rejected

theorem add_missing {store : Relation Root ByteArray} (bound : Binding store) (root : Root)
    (absent : ¬ ∃ bytes, store root bytes) (bytes : ByteArray) :
    Binding (union store (fun other value => other = root ∧ value = bytes)) := by
  intro other left right first second
  rcases first with first | ⟨atRoot, leftEq⟩ <;> rcases second with second | ⟨otherRoot, rightEq⟩
  · exact bound first second
  · exact (absent ⟨left, otherRoot ▸ first⟩).elim
  · exact (absent ⟨right, atRoot ▸ second⟩).elim
  · exact leftEq.trans rightEq.symm

omit [LinearOrder Name] in
theorem rekey_binding_iff (rename : Name → Root) (store : Relation Name Repr) :
    Binding (rekeyNames rename store) ↔ ∀ ⦃first second left right⦄,
      rename first = rename second → store first left → store second right → left = right := by
  constructor
  · intro bound first second left right same hl hr
    exact bound ⟨first, rfl, hl⟩ ⟨second, same.symm, hr⟩
  · rintro compatible _ _ _ ⟨first, hl, pair⟩ ⟨second, hr, otherPair⟩
    exact compatible (hl.trans hr.symm) pair otherPair

end Silmaril.Proofs.Formats.Dasl.PartitionValidity
