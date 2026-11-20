module

public import Silmaril.Formats.Cbor.Drisl.Cid.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl.Cid

open Silmaril.Formats.Cbor.Drisl

theorem render_read {Link : Type} (codec : CidCodec Link)
    (sound : ∀ {bytes cid}, codec.parse? bytes = some cid → codec.bytes cid = bytes)
    {text : String} {cid : Link} (accepted : codec.read? text = some cid) : codec.render cid = text := by
  cases shape : text.toList with
  | nil => simp [CidCodec.read?, shape] at accepted
  | cons head digits =>
    by_cases correct : head = 'b'
    · subst head
      have readDigits : (Base32.decodeChars cidAlphabet false digits).bind codec.parse? = some cid := by
        simpa [CidCodec.read?, shape] using accepted
      obtain ⟨bytes, parsed, readCid⟩ := Option.bind_eq_some_iff.mp readDigits
      have encoded := (Base32.decodeChars_eq_some_iff cidAlphabet false).mp parsed
      apply String.toList_inj.mp
      simp [CidCodec.render, sound readCid, encoded, shape]
    · simp [CidCodec.read?, shape, correct] at accepted

theorem parse_sound {profile : CidProfile} {bytes : List UInt8} {cid : Cid profile}
    (accepted : (Cid.codec profile).parse? bytes = some cid) : (Cid.codec profile).bytes cid = bytes := by
  by_cases valid : profile.accepts bytes = true
  · have same : (⟨bytes, valid⟩ : Cid profile) = cid := by simpa [Cid.codec, valid] using accepted
    exact (congrArg Subtype.val same).symm
  · simp [Cid.codec, valid] at accepted

end Silmaril.Proofs.Formats.Cbor.Drisl.Cid
