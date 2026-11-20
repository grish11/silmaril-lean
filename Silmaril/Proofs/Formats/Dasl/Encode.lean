module

public import Silmaril.Formats.Dasl.Encode.Defs
public import Silmaril.Semantics.Naming.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Encode

open Silmaril.Formats.Dasl.Encode Silmaril.Semantics.Naming

variable {Source Target Name Wire : Type}

theorem fields_roundtrip (codec : TotalCodec Source Target) (fields : Fields Source) :
    (fields.map codec.encode).traverse? codec.decode? = some fields := by
  cases fields with
  | mk keys values =>
    have present : ∀ key (member : key ∈ keys), (codec.decode? (codec.encode (values ⟨key, member⟩))).isSome = true :=
      fun _ _ => by rw [codec.recovers]; rfl
    unfold Fields.traverse?
    refine (dite_eq_left ?_).trans ?_
    · exact present
    · apply congrArg some
      apply congrArg (Fields.mk keys)
      funext key
      exact Option.some.inj ((Option.some_get _).trans (codec.recovers (values key)))

theorem list_roundtrip (codec : TotalCodec Source Target) (items : List Source) :
    codec.partial.listDecode (codec.listEncode items) = some items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp [TotalCodec.listEncode, PartialCodec.listDecode, TotalCodec.partial, codec.recovers] at ih ⊢
    simp [ih]

theorem partial_list_roundtrip (codec : PartialCodec Source Target) {items : List Source} {encoded : List Target}
    (hit : codec.listEncode items = some encoded) : codec.listDecode encoded = some items := by
  induction items generalizing encoded with
  | nil => cases hit; rfl
  | cons head tail ih =>
    cases first : codec.encode? head with
    | none => simp [PartialCodec.listEncode, first] at hit
    | some target =>
      cases rest : codec.listEncode tail with
      | none => simp [PartialCodec.listEncode, first, show tail.mapM codec.encode? = none from rest] at hit
      | some targets =>
        have same : target :: targets = encoded := by
          simpa [PartialCodec.listEncode, first, show tail.mapM codec.encode? = some targets from rest] using hit
        subst encoded
        have decoded := ih rest
        simp [PartialCodec.listDecode, codec.recovers first, show targets.mapM codec.decode? = some tail from decoded]

theorem coded_unique {raw : Relation Name Target} {codec : PartialCodec Source Target}
    (unique : UniqueNames raw) : UniqueNames (codedNames raw codec) := by
  rintro _ _ _ ⟨left, first, leftEncoded⟩ ⟨right, second, rightEncoded⟩
  have same : left = right := Option.some.inj (leftEncoded.symm.trans rightEncoded)
  exact unique first (same ▸ second)

theorem coded_unique_of_hash {raw : Relation Name Target} {codec : PartialCodec Source Target}
    (serialize : Target → Option Wire) (hash : Wire → Name)
    (checked : HashCompatible hash (push raw (graph serialize)))
    (renders : ∀ ⦃source repr⦄, codec.rel repr source → ∃ wire, serialize repr = some wire) :
    UniqueNames (codedNames raw codec) := by
  rintro _ _ _ ⟨left, first, leftEncoded⟩ ⟨right, second, rightEncoded⟩
  have same : left = right := Option.some.inj (leftEncoded.symm.trans rightEncoded)
  obtain ⟨wire, rendered⟩ := renders leftEncoded
  exact (checked ⟨left, first, rendered⟩).symm.trans (checked ⟨left, same ▸ second, rendered⟩)

end Silmaril.Proofs.Formats.Dasl.Encode
