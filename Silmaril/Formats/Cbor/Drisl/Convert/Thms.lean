module

public import Silmaril.Formats.Cbor.Drisl.Convert.Defs
import Silmaril.Proofs.Formats.Cbor.Drisl.Convert

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

theorem removeLinks_embedI64 {Link : Type} (value : JsonWithBytes.OrderedI64) :
    removeLinks? (embedI64 (Cid := Link) value) = some value :=
  Proofs.Formats.Cbor.Drisl.Convert.remove_embed value

theorem narrowATProto_widen {Link : Type} (value : OrderedATProto Link) :
    narrowATProto? (widenATProto value) = some value :=
  Proofs.Formats.Cbor.Drisl.Convert.narrow_widen value

theorem embedI64_removeLinks {Link : Type} {source : OrderedATProto Link}
    {value : JsonWithBytes.OrderedI64} (readBack : removeLinks? source = some value) :
    embedI64 value = source := Proofs.Formats.Cbor.Drisl.Convert.embed_of_remove source value readBack

theorem removeLinks_isSome_iff {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) : (removeLinks? value).isSome ↔ links value = [] :=
  Proofs.Formats.Cbor.Drisl.Convert.isSome_iff_links_empty value

theorem linkFree_i64_iff {Link : Type} (source : OrderedATProto Link) :
    links source = [] ↔ ∃ value : JsonWithBytes.OrderedI64, embedI64 value = source := by
  rw [← removeLinks_isSome_iff, Option.isSome_iff_exists]
  exact ⟨fun ⟨value, readBack⟩ => ⟨value, embedI64_removeLinks readBack⟩,
    fun ⟨value, same⟩ => ⟨value, same ▸ removeLinks_embedI64 value⟩⟩

theorem restrictToI64_iff {Link : Type} (result : Option (OrderedATProto Link))
    (value : JsonWithBytes.OrderedI64) : result.bind removeLinks? = some value ↔ result = some (embedI64 value) := by
  refine ⟨?_, fun same => same ▸ removeLinks_embedI64 value⟩
  rintro (h : _)
  obtain ⟨source, read, removed⟩ := Option.bind_eq_some_iff.mp h
  exact read.trans (congrArg some (embedI64_removeLinks removed).symm)

end Silmaril.Formats.Cbor.Drisl
