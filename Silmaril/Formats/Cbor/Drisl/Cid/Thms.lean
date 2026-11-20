module

public import Silmaril.Formats.Cbor.Drisl.Cid.Defs
import Silmaril.Proofs.Formats.Cbor.Drisl.Cid

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

theorem Cid.parse_bytes (profile : CidProfile) (cid : Cid profile) :
    (Cid.codec profile).parse? ((Cid.codec profile).bytes cid) = some cid := by
  simp [Cid.codec, cid.property]

theorem CidCodec.read_render {Link : Type} (codec : CidCodec Link)
    (inverse : ∀ cid, codec.parse? (codec.bytes cid) = some cid) (cid : Link) :
    codec.read? (codec.render cid) = some cid := by
  simp [CidCodec.read?, CidCodec.render, inverse]

theorem Cid.read_render (profile : CidProfile) (cid : Cid profile) :
    (Cid.codec profile).read? ((Cid.codec profile).render cid) = some cid :=
  CidCodec.read_render _ (Cid.parse_bytes profile) cid

theorem Cid.read_eq_some_iff {profile : CidProfile} {text : String} {cid : Cid profile} :
    (Cid.codec profile).read? text = some cid ↔ (Cid.codec profile).render cid = text :=
  ⟨Proofs.Formats.Cbor.Drisl.Cid.render_read _ (fun h => Proofs.Formats.Cbor.Drisl.Cid.parse_sound h),
    fun same => same ▸ Cid.read_render profile cid⟩

end Silmaril.Formats.Cbor.Drisl
