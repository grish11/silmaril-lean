module

public import Silmaril.Formats.Dasl.Encode.Partition.Validity.Defs
import Silmaril.Proofs.Formats.Dasl.PartitionValidity

public section

namespace Silmaril.Formats.Dasl.Encode.Partition

open Silmaril.Semantics Naming

variable {Name Root Repr : Type} [LinearOrder Name]

theorem Exact.sound {labels : OrderedMap Name Name} {spec : PER Name} (exactly : Exact labels spec) :
    Sound labels spec := exactly ▸ le_rfl

theorem Exact.sameSupport {labels : OrderedMap Name Name} {spec : PER Name} (exactly : Exact labels spec) :
    SameSupport labels spec := fun name => (PER.Partition.map_dom_iff_key labels name).symm.trans (exactly ▸ Iff.rfl)

theorem Sound.support_included {labels : OrderedMap Name Name} {spec : PER Name} (sound : Sound labels spec)
    {name : Name} (present : name ∈ labels.keySet) : spec.Dom name :=
  sound ((PER.Partition.map_dom_iff_key labels name).mpr present)

theorem normalize_exact_iff (labels : OrderedMap Name Name) (spec : PER Name) :
    Exact (PER.Partition.normalize labels) spec ↔ Exact labels spec := by simp only [Exact, PER.Partition.normalize_partition]

theorem normalize_sound_iff (labels : OrderedMap Name Name) (spec : PER Name) :
    Sound (PER.Partition.normalize labels) spec ↔ Sound labels spec := by simp only [Sound, PER.Partition.normalize_partition]

theorem normalize_sameSupport_iff (labels : OrderedMap Name Name) (spec : PER Name) :
    SameSupport (PER.Partition.normalize labels) spec ↔ SameSupport labels spec := by
  simp only [SameSupport, ← PER.Partition.map_dom_iff_key, PER.Partition.normalize_partition]

theorem valid_encoded (accepts : OrderedMap Name Name → Prop) (codec : PartialCodec (OrderedMap Name Name) Repr)
    {labels : OrderedMap Name Name} {repr : Repr} (hit : codec.encode? labels = some repr) :
    Valid accepts codec repr ↔ accepts labels :=
  ⟨fun ⟨_, decoded, h⟩ => Option.some.inj (decoded.symm.trans (codec.recovers hit)) ▸ h,
   fun h => ⟨labels, codec.recovers hit, h⟩⟩

theorem namedMaps_binding (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    {store : Relation Root ByteArray} (bound : Binding store) : Binding (namedMaps profile name store) :=
  (bound.project _).subset fun _ _ hit => hit.2

theorem namedValid_iff_namedEncodingValid (accepts : OrderedMap Name Name → Prop) (profile : Wire.Profile Root)
    (name : TotalCodec Name (Shallow Root)) [DecidableEq (OrderedMap Name Name)]
    (store : Relation Root ByteArray) (root : Root) : NamedValid accepts profile name store root ↔
      profile.objectName root = true ∧ NamedEncodingValid accepts (profile.codec (nameMap name)) store root :=
  ⟨fun ⟨labels, ⟨guard, bytes, hit, decoded⟩, valid⟩ => ⟨guard, bytes, hit, labels, decoded, valid⟩,
    fun ⟨guard, bytes, hit, labels, decoded, valid⟩ => ⟨labels, ⟨guard, bytes, hit, decoded⟩, valid⟩⟩

theorem namedMaps_mono (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    {store extension : Relation Root ByteArray} (incl : Subset store extension) :
    Subset (namedMaps profile name store) (namedMaps profile name extension) :=
  fun _ _ ⟨guard, bytes, hit, decoded⟩ => ⟨guard, bytes, incl hit, decoded⟩

theorem namedValid_mono (accepts : OrderedMap Name Name → Prop) (profile : Wire.Profile Root)
    (name : TotalCodec Name (Shallow Root)) {store extension : Relation Root ByteArray} (incl : Subset store extension)
    {root : Root} (hit : NamedValid accepts profile name store root) : NamedValid accepts profile name extension root :=
  let ⟨labels, named, valid⟩ := hit; ⟨labels, namedMaps_mono profile name incl named, valid⟩

theorem namedMaps_of_root (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    [DecidableEq (OrderedMap Name Name)] {store : Relation Root ByteArray} {root : Root} {labels : OrderedMap Name Name}
    (hit : profile.roots (nameMap name) store root labels) : namedMaps profile name store root labels :=
  let ⟨guard, bytes, stored, encoded⟩ := hit
  ⟨guard, bytes, stored, (profile.codec (nameMap name)).recovers encoded⟩

theorem observe_decoded_iff (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (read : Root → Option ByteArray) (root : Root) (labels : OrderedMap Name Name) :
    observeNamed profile name read root = .decoded labels ↔ namedMaps profile name (graph read) root labels :=
  Proofs.Formats.Dasl.PartitionValidity.decoded_iff profile name read root labels

theorem observe_unknown_iff (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (read : Root → Option ByteArray) (root : Root) :
    observeNamed profile name read root = .unknown ↔ profile.objectName root = true ∧ read root = none :=
  Proofs.Formats.Dasl.PartitionValidity.unknown_iff profile name read root

theorem rejected_in_extension (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    {read : Root → Option ByteArray} {store : Relation Root ByteArray} {root : Root}
    (incl : Subset (graph read) store) (bound : Binding store)
    (rejected : observeNamed profile name read root = .rejected) (labels : OrderedMap Name Name) :
    ¬ namedMaps profile name store root labels :=
  Proofs.Formats.Dasl.PartitionValidity.rejected_extension profile name incl bound rejected labels

/-- A missing observation is compatible with any otherwise admissible payload
at the unbound root. It does not refute a proposed PER. -/
theorem missing_can_extend (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    {store : Relation Root ByteArray} (bound : Binding store) {root : Root} {bytes : ByteArray}
    (absent : ¬ ∃ data, store root data) (guard : profile.objectName root = true)
    {labels : OrderedMap Name Name} (decoded : profile.decode? (nameMap name) bytes = some labels) :
    ∃ extension, Subset store extension ∧ Binding extension ∧ namedMaps profile name extension root labels :=
  ⟨union store (fun other value => other = root ∧ value = bytes), fun _ _ h => .inl h,
    Proofs.Formats.Dasl.PartitionValidity.add_missing bound root absent bytes, guard, bytes, .inr ⟨rfl, rfl⟩, decoded⟩

omit [LinearOrder Name] in
theorem rekey_binding_iff (rename : Name → Root) (store : Relation Name Repr) :
    Binding (rekeyNames rename store) ↔ ∀ ⦃first second left right⦄,
      rename first = rename second → store first left → store second right → left = right :=
  Proofs.Formats.Dasl.PartitionValidity.rekey_binding_iff rename store

omit [LinearOrder Name] in
theorem rekey_binding_of_injective {rename : Name → Root} {store : Relation Name Repr}
    (injective : Function.Injective rename) (bound : Binding store) : Binding (rekeyNames rename store) :=
  (rekey_binding_iff rename store).mpr fun _ _ _ _ same first second => bound first (injective same ▸ second)

end Silmaril.Formats.Dasl.Encode.Partition
