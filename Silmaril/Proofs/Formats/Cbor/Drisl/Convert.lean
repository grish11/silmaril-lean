module

public import Silmaril.Formats.Cbor.Drisl.Convert.Defs
public import Silmaril.Formats.Cbor.Drisl.Number.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl.Convert

open Silmaril.Formats Silmaril.Formats.Cbor.Drisl

theorem remove_embed {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (JsonWithBytes.Scalar Numeric) index) :
    removeLinks? (value.mapScalar (Scalar.data (Cid := Link))) = some value := by
  induction value <;> simp_all [removeLinks?, JsonWithBytes.traverse?]

theorem embed_of_remove {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) :
    ∀ result, removeLinks? value = some result → result.mapScalar Scalar.data = value := by
  induction value with
  | scalar atom =>
    cases atom <;> simp [removeLinks?, JsonWithBytes.traverse?]
  | nil | objNil =>
    intro result valid
    cases valid
    rfl
  | list items ih | map items ih =>
    intro result valid
    change ((_ <$> removeLinks? items) : Option _) = some result at valid
    obtain ⟨inner, decoded, rfl⟩ := Option.map_eq_some_iff.mp valid
    simp [ih inner decoded]
  | cons value tail ih tailIH =>
    intro result valid
    change ((removeLinks? value).bind fun inner => (removeLinks? tail).bind fun rest =>
      some (.cons inner rest)) = some result at valid
    rcases Option.bind_eq_some_iff.mp valid with ⟨inner, readInner, next⟩
    rcases Option.bind_eq_some_iff.mp next with ⟨rest, readRest, same⟩
    cases same
    simp [ih inner readInner, tailIH rest readRest]
  | objCons name value tail ih tailIH =>
    intro result valid
    change ((removeLinks? value).bind fun inner => (removeLinks? tail).bind fun rest =>
      some (.objCons name inner rest)) = some result at valid
    rcases Option.bind_eq_some_iff.mp valid with ⟨inner, readInner, next⟩
    rcases Option.bind_eq_some_iff.mp next with ⟨rest, readRest, same⟩
    cases same
    simp [ih inner readInner, tailIH rest readRest]

theorem isSome_iff_links_empty {Numeric Link : Type} {index : JsonIx}
    (value : RawSyn String (Scalar Numeric Link) index) :
    (removeLinks? value).isSome ↔ links value = [] := by
  induction value with
  | scalar atom => cases atom <;> simp [removeLinks?, JsonWithBytes.traverse?, links, RawSyn.scalars]
  | list items ih | map items ih => simpa [removeLinks?, JsonWithBytes.traverse?, links, RawSyn.scalars] using ih
  | nil | objNil => simp [removeLinks?, JsonWithBytes.traverse?, links, RawSyn.scalars]
  | cons value tail ih tailIH | objCons _ value tail ih tailIH =>
    cases headEq : removeLinks? value <;> cases tailEq : removeLinks? tail <;>
      simp_all [removeLinks?, JsonWithBytes.traverse?, links, RawSyn.scalars, List.filterMap_append]

theorem narrow_widen {Link : Type} {index : JsonIx} (value : RawSyn String (Scalar Int64 Link) index) :
    JsonWithBytes.traverse? some narrowScalar? (value.mapScalar widenScalar) = some value := by
  induction value with
  | scalar atom =>
    cases atom with
    | data atom => cases atom <;> simp [JsonWithBytes.traverse?, widenScalar, narrowScalar?, mapNumber?,
        Integer.toInt_ofInt64, int64_toInt]
    | link => rfl
  | list _ ih | map _ ih => simp [JsonWithBytes.traverse?, ih]
  | nil | objNil => rfl
  | cons _ _ ih tailIH | objCons _ _ _ ih tailIH => simp [JsonWithBytes.traverse?, ih, tailIH]

end Silmaril.Proofs.Formats.Cbor.Drisl.Convert
