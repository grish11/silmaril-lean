module

public import Silmaril.Formats.Cbor.Drisl.Debug.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl.Debug

open Silmaril.Formats Silmaril.Formats.Cbor.Drisl Silmaril.Formats.Cbor.Drisl.Debug

theorem readKeyChars_keyChars (policy : Escape) (chars : List Char) :
    policy.readKeyChars? (policy.keyChars chars) = some chars := by
  cases policy <;> cases chars with
  | nil => rfl
  | cons head tail =>
    by_cases headDollar : head = '$'
    · subst head
      simp [Escape.keyChars, Escape.readKeyChars?]
    · simp [Escape.keyChars, Escape.readKeyChars?, headDollar]

theorem readKey_key (policy : Escape) (name : String) : policy.readKey? (policy.key name) = some name := by
  simp [Escape.readKey?, Escape.key, readKeyChars_keyChars]

theorem key_not_reserved (policy : Escape) (escaped : policy ≠ .none) (name : String) :
    Wrapper.ofKey? (policy.key name) = none := by
  have readBack := readKey_key policy name
  have bytesBad : policy.readKey? Wrapper.bytes.key = none := by
    cases policy <;> first | contradiction | decide
  have linkBad : policy.readKey? Wrapper.link.key = none := by
    cases policy <;> first | contradiction | decide
  have notBytes : policy.key name ≠ Wrapper.bytes.key := fun same => by
    rw [same, bytesBad] at readBack
    contradiction
  have notLink : policy.key name ≠ Wrapper.link.key := fun same => by
    rw [same, linkBad] at readBack
    contradiction
  simp [Wrapper.ofKey?, notBytes, notLink]

theorem escaped_safe (policy : Escape) (escaped : policy ≠ .none)
    {Numeric Link : Type} {index : JsonIx} (value : RawSyn String (Scalar Numeric Link) index) :
    CollisionFree policy value := by
  induction value with
  | map fields ih =>
    refine ⟨?_, ih⟩
    cases fields with
    | objNil => trivial
    | objCons name value tail =>
      cases tail with
      | objNil => exact key_not_reserved policy escaped name
      | objCons => trivial
  | scalar | nil | objNil => trivial
  | list _ ih => exact ih
  | cons _ _ ih tailIH | objCons _ _ _ ih tailIH => exact ⟨ih, tailIH⟩

theorem wrapper_encode_eq_none {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (policy : Escape) (fields : RawSyn String (Scalar Input Link) .obj)
    (safe : SafeObject policy fields) : wrapper? (encode codec policy fields) = none := by
  cases fields with
  | objNil => rfl
  | objCons name value tail =>
    cases tail with
    | objNil => simp [wrapper?, encode, show Wrapper.ofKey? (policy.key name) = none from safe]
    | objCons => rfl

theorem decode_encode {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) {index : JsonIx} (value : RawSyn String (Scalar Input Link) index)
    (safe : CollisionFree policy value) : decode? codec policy (encode codec policy value) = some value := by
  induction value with
  | scalar value =>
    cases value with
    | data atom =>
      cases atom <;> simp [encode, decode?, wrap, readWrapper?, wrapper?, numberInv,
        Wrapper.ofKey?, Wrapper.key, Function.comp_def]
    | link cid => simp [encode, decode?, wrap, readWrapper?, wrapper?, linkInv,
        Wrapper.ofKey?, Wrapper.key, Function.comp_def]
  | map fields ih =>
    simp [encode, decode?, wrapper_encode_eq_none codec policy fields safe.1, ih safe.2]
  | list items ih => simp [encode, decode?, ih safe]
  | nil | objNil => rfl
  | cons value tail ih tailIH => simp [encode, decode?, ih safe.1, tailIH safe.2]
  | objCons name value tail ih tailIH =>
    simp [encode, decode?, readKey_key, ih safe.1, tailIH safe.2]

theorem keysSatisfy_mono {Key Atom : Type} {left right : Key → Prop}
    (implies : ∀ name, left name → right name) {index : JsonIx} (value : RawSyn Key Atom index)
    (valid : KeysSatisfy left value) : KeysSatisfy right value := by
  induction value with
  | scalar | nil | objNil => trivial
  | list _ ih | map _ ih => exact ih valid
  | cons _ _ ih tailIH => exact ⟨ih valid.1, tailIH valid.2⟩
  | objCons name _ _ ih tailIH => exact ⟨implies name valid.1, ih valid.2.1, tailIH valid.2.2⟩

theorem keysSatisfy_mapScalar {Key Input Output : Type} (allowed : Key → Prop) (fn : Input → Output)
    {index : JsonIx} (value : RawSyn Key Input index) :
    KeysSatisfy allowed (value.mapScalar fn) ↔ KeysSatisfy allowed value := by
  induction value <;> simp_all [KeysSatisfy]

theorem reserved_safe {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) (valid : KeysSatisfy NoReserved value) :
    CollisionFree .none value := by
  induction value with
  | scalar | nil | objNil => trivial
  | list _ ih => exact ih valid
  | cons _ _ ih tailIH => exact ⟨ih valid.1, tailIH valid.2⟩
  | objCons _ _ _ ih tailIH => exact ⟨ih valid.2.1, tailIH valid.2.2⟩
  | map fields ih =>
    refine ⟨?_, ih valid⟩
    cases fields with
    | objNil => trivial
    | objCons name value tail =>
      cases tail with
      | objNil => simpa [SafeObject, Escape.key, Escape.keyChars, NoReserved] using valid.1
      | objCons => trivial

theorem noDollar_not_reserved (name : String) (valid : NoDollar name) : NoReserved name := by
  have notBytes : name ≠ Wrapper.bytes.key := fun same => valid "bytes".toList (by rw [same]; decide)
  have notLink : name ≠ Wrapper.link.key := fun same => valid "link".toList (by rw [same]; decide)
  simp [NoReserved, Wrapper.ofKey?, notBytes, notLink]

theorem key_noDollar (policy : Escape) (name : String) (valid : NoDollar name) : policy.key name = name := by
  unfold Escape.key
  have unchanged : policy.keyChars name.toList = name.toList := by
    cases shape : name.toList with
    | nil => cases policy <;> rfl
    | cons head tail =>
      have notDollar : head ≠ '$' := fun same => valid tail (same ▸ shape)
      cases policy <;> simp [Escape.keyChars, notDollar]
  rw [unchanged, String.ofList_toList]

theorem policies_agree {Input Numeric Link : Type} (codec : Codec Input Numeric Link)
    (left right : Escape) {index : JsonIx} (value : RawSyn String (Scalar Input Link) index)
    (valid : KeysSatisfy NoDollar value) : encode codec left value = encode codec right value := by
  induction value with
  | scalar value => cases value with
    | data atom => cases atom <;> rfl
    | link => rfl
  | nil | objNil => rfl
  | list _ ih | map _ ih => simp [encode, ih valid]
  | cons _ _ ih tailIH => simp [encode, ih valid.1, tailIH valid.2]
  | objCons name _ _ ih tailIH =>
    simp [encode, key_noDollar _ name valid.1, ih valid.2.1, tailIH valid.2.2]

end Silmaril.Proofs.Formats.Cbor.Drisl.Debug
