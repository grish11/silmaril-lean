module

public import Silmaril.Formats.JsonNumbers.Defs
public import Silmaril.Formats.JsonBytes.Thms

/-! # Proofs: JSON texts with a number-token language (`Silmaril.Formats.JsonNumbers.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonNumbers

open RegularExpression Silmaril.Formats.Utf8 Silmaril.Formats.JsonBytes
open Silmaril.Formats.JsonNumbers

/-! ## The RFC number language gives the RFC grammar -/

theorem mem_scalar_iff {p : Profile} {w : List UInt8} :
    w ∈ (scalar p).matches' ↔ w ∈ (literal p).matches' ∨ w ∈ number.matches' := by
  simp only [Formats.JsonBytes.scalar, literal, matches'_add, Language.mem_add]
  tauto

mutual

theorem value_toBytes {p : Profile} {w : List UInt8} :
    Formats.JsonNumbers.Value p rfc w → Formats.JsonBytes.Value p w
  | .literal h => .scalar (mem_scalar_iff.mpr (Or.inl h))
  | .number h => .scalar (mem_scalar_iff.mpr (Or.inr h))
  | .emptyArray ha hb => .emptyArray ha hb
  | .array ha hx hb => .array ha (elements_toBytes hx) hb
  | .emptyObject ha hb => .emptyObject ha hb
  | .object ha hm hb => .object ha (members_toBytes hm) hb

theorem elements_toBytes {p : Profile} {w : List UInt8} :
    Formats.JsonNumbers.Elements p rfc w → Formats.JsonBytes.Elements p w
  | .one hv => .one (value_toBytes hv)
  | .cons hv hs hx => .cons (value_toBytes hv) hs (elements_toBytes hx)

theorem members_toBytes {p : Profile} {w : List UInt8} :
    Formats.JsonNumbers.Members p rfc w → Formats.JsonBytes.Members p w
  | .one hk hc hv => .one hk hc (value_toBytes hv)
  | .cons hk hc hv hs hm => .cons hk hc (value_toBytes hv) hs (members_toBytes hm)

end

mutual

theorem value_ofBytes {p : Profile} {w : List UInt8} :
    Formats.JsonBytes.Value p w → Formats.JsonNumbers.Value p rfc w
  | .scalar h => (mem_scalar_iff.mp h).elim .literal .number
  | .emptyArray ha hb => .emptyArray ha hb
  | .array ha hx hb => .array ha (elements_ofBytes hx) hb
  | .emptyObject ha hb => .emptyObject ha hb
  | .object ha hm hb => .object ha (members_ofBytes hm) hb

theorem elements_ofBytes {p : Profile} {w : List UInt8} :
    Formats.JsonBytes.Elements p w → Formats.JsonNumbers.Elements p rfc w
  | .one hv => .one (value_ofBytes hv)
  | .cons hv hs hx => .cons (value_ofBytes hv) hs (elements_ofBytes hx)

theorem members_ofBytes {p : Profile} {w : List UInt8} :
    Formats.JsonBytes.Members p w → Formats.JsonNumbers.Members p rfc w
  | .one hk hc hv => .one hk hc (value_ofBytes hv)
  | .cons hk hc hv hs hm => .cons hk hc (value_ofBytes hv) hs (members_ofBytes hm)

end

theorem language_rfc (p : Profile) :
    Formats.JsonNumbers.language p rfc = Formats.JsonBytes.language p := by
  ext w
  constructor
  · rintro ⟨a, v, b, ha, hv, hb, rfl⟩; exact ⟨a, v, b, ha, value_toBytes hv, hb, rfl⟩
  · rintro ⟨a, v, b, ha, hv, hb, rfl⟩; exact ⟨a, v, b, ha, value_ofBytes hv, hb, rfl⟩

/-! ## Monotonicity in the profile and the number language -/

theorem literal_le {p q : Profile} (hs : (string p).matches' ≤ (string q).matches') :
    (literal p).matches' ≤ (literal q).matches' := by
  intro w h
  simp only [literal, matches'_add] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (hs h)

mutual

theorem value_mono {p q : Profile} {N M : Language UInt8}
    (hs : (string p).matches' ≤ (string q).matches') (hN : N ≤ M) {w : List UInt8} :
    Formats.JsonNumbers.Value p N w → Formats.JsonNumbers.Value q M w
  | .literal h => .literal (literal_le hs h)
  | .number h => .number (hN h)
  | .emptyArray ha hb => .emptyArray ha hb
  | .array ha hx hb => .array ha (elements_mono hs hN hx) hb
  | .emptyObject ha hb => .emptyObject ha hb
  | .object ha hm hb => .object ha (members_mono hs hN hm) hb

theorem elements_mono {p q : Profile} {N M : Language UInt8}
    (hs : (string p).matches' ≤ (string q).matches') (hN : N ≤ M) {w : List UInt8} :
    Formats.JsonNumbers.Elements p N w → Formats.JsonNumbers.Elements q M w
  | .one hv => .one (value_mono hs hN hv)
  | .cons hv hs' hx => .cons (value_mono hs hN hv) hs' (elements_mono hs hN hx)

theorem members_mono {p q : Profile} {N M : Language UInt8}
    (hs : (string p).matches' ≤ (string q).matches') (hN : N ≤ M) {w : List UInt8} :
    Formats.JsonNumbers.Members p N w → Formats.JsonNumbers.Members q M w
  | .one hk hc hv => .one (hs hk) hc (value_mono hs hN hv)
  | .cons hk hc hv hs' hm => .cons (hs hk) hc (value_mono hs hN hv) hs' (members_mono hs hN hm)

end

theorem language_mono' {p q : Profile} {N M : Language UInt8}
    (hs : (string p).matches' ≤ (string q).matches') (hN : N ≤ M) :
    Formats.JsonNumbers.language p N ≤ Formats.JsonNumbers.language q M := by
  rintro w ⟨a, v, b, ha, hv, hb, rfl⟩
  exact ⟨a, v, b, ha, value_mono hs hN hv, hb, rfl⟩

end Silmaril.Proofs.Formats.JsonNumbers

end
