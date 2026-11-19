module

public import Silmaril.Formats.Cbor.Drisl.Debug.Defs
import Silmaril.Proofs.Formats.Cbor.Drisl.Debug

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl.Debug

theorem readKey_key (policy : Escape) (name : String) : policy.readKey? (policy.key name) = some name :=
  Proofs.Formats.Cbor.Drisl.Debug.readKey_key policy name

theorem escaped_safe (policy : Escape) (escaped : policy ≠ .none)
    {Numeric Link : Type} {index : JsonIx} (value : RawSyn String (Scalar Numeric Link) index) :
    CollisionFree policy value :=
  Proofs.Formats.Cbor.Drisl.Debug.escaped_safe policy escaped value

theorem reserved_safe {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) (valid : KeysSatisfy NoReserved value) :
    CollisionFree .none value := Proofs.Formats.Cbor.Drisl.Debug.reserved_safe value valid

theorem noDollar_noReserved {KeyAtom : Type} {index : JsonIx} (value : RawSyn String KeyAtom index)
    (valid : KeysSatisfy NoDollar value) : KeysSatisfy NoReserved value :=
  Proofs.Formats.Cbor.Drisl.Debug.keysSatisfy_mono
    Proofs.Formats.Cbor.Drisl.Debug.noDollar_not_reserved value valid

theorem keysSatisfy_mapScalar {Key Input Output : Type} (allowed : Key → Prop) (fn : Input → Output)
    {index : JsonIx} (value : RawSyn Key Input index) :
    KeysSatisfy allowed (value.mapScalar fn) ↔ KeysSatisfy allowed value :=
  Proofs.Formats.Cbor.Drisl.Debug.keysSatisfy_mapScalar allowed fn value

theorem policies_agree {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (left right : Escape) {index : JsonIx} (value : RawSyn String (Scalar Input Link) index)
    (valid : KeysSatisfy NoDollar value) : encode codec left value = encode codec right value :=
  Proofs.Formats.Cbor.Drisl.Debug.policies_agree codec left right value valid

theorem decode_encode {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) {index : JsonIx} (value : RawSyn String (Scalar Input Link) index)
    (safe : CollisionFree policy value) : decode? codec policy (encode codec policy value) = some value :=
  Proofs.Formats.Cbor.Drisl.Debug.decode_encode codec numberInv linkInv policy value safe

theorem decode_encode_escaped {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) (escaped : policy ≠ .none) {index : JsonIx}
    (value : RawSyn String (Scalar Input Link) index) :
    decode? codec policy (encode codec policy value) = some value :=
  decode_encode codec numberInv linkInv policy value (escaped_safe policy escaped value)

theorem encode_injective {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) {index : JsonIx} {left right : RawSyn String (Scalar Input Link) index}
    (leftSafe : CollisionFree policy left) (rightSafe : CollisionFree policy right)
    (same : encode codec policy left = encode codec policy right) : left = right :=
  Option.some.inj ((decode_encode codec numberInv linkInv policy left leftSafe).symm.trans
    ((congrArg (decode? codec policy) same).trans (decode_encode codec numberInv linkInv policy right rightSafe)))

/-- Right inverse on the collision-free image (including the full escaped image). -/
theorem encode_decode_on_image {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) {index : JsonIx} (value : RawSyn String (Scalar Input Link) index)
    (safe : CollisionFree policy value) :
    (decode? codec policy (encode codec policy value)).map (encode codec policy) =
      some (encode codec policy value) := by
  rw [decode_encode codec numberInv linkInv policy value safe, Option.map_some]

end Silmaril.Formats.Cbor.Drisl.Debug
