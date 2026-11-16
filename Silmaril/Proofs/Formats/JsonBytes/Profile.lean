module

public import Silmaril.Formats.JsonBytes.Defs
public import Silmaril.Formats.Utf8.Thms

/-! # Proofs: the scalar-escape profile refines the RFC 8259 profile
(`Silmaril.Formats.JsonBytes.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonBytes.Profile

open RegularExpression Silmaril.Formats.Utf8 Silmaril.Formats.JsonBytes
open scoped Computability

theorem anyOf_le {l : List UInt8} {r : RegularExpression UInt8}
    (h : ∀ b ∈ l, r.rmatch [b] = true) : (anyOf l).matches' ≤ r.matches' := by
  intro w hw
  obtain ⟨b, hb, rfl⟩ := mem_anyOf.mp hw
  exact (rmatch_iff_matches' _ _).mp (h b hb)

theorem hexD_le : hexD.matches' ≤ hexdig.matches' := anyOf_le (by decide +kernel)

theorem highEscape_le : highEscape.matches' ≤ unitEscape.matches' := by
  show uPrefix.matches' * hexD.matches' * (anyOf _).matches' * hexdig.matches' *
      hexdig.matches' ≤ uPrefix.matches' * hexdig.matches' * hexdig.matches' *
      hexdig.matches' * hexdig.matches'
  gcongr
  · exact hexD_le
  · exact anyOf_le (by decide +kernel)

theorem lowEscape_le : lowEscape.matches' ≤ unitEscape.matches' := by
  show uPrefix.matches' * hexD.matches' * (anyOf _).matches' * hexdig.matches' *
      hexdig.matches' ≤ uPrefix.matches' * hexdig.matches' * hexdig.matches' *
      hexdig.matches' * hexdig.matches'
  gcongr
  · exact hexD_le
  · exact anyOf_le (by decide +kernel)

theorem bmpEscape_le : bmpEscape.matches' ≤ unitEscape.matches' := by
  show uPrefix.matches' * (((digit.matches' + (anyOf _).matches') * hexdig.matches' *
      hexdig.matches' * hexdig.matches') + hexD.matches' * (byteRange 0x30 0x37).matches' *
      hexdig.matches' * hexdig.matches') ≤ uPrefix.matches' * hexdig.matches' *
      hexdig.matches' * hexdig.matches' * hexdig.matches'
  rw [mul_add]
  refine sup_le ?_ ?_
  · simp only [← mul_assoc]
    gcongr
    exact sup_le (anyOf_le (by decide +kernel)) (anyOf_le (by decide +kernel))
  · simp only [← mul_assoc]
    gcongr
    · exact hexD_le
    · exact anyOf_le (by decide +kernel)

/-- One character of the scalar-escape profile is a sequence of RFC 8259 characters. -/
theorem strChar_le : (strChar .scalarEscapes).matches' ≤ (strChar .rfc8259).matches'∗ := by
  show (unescaped.matches' + shortEscape.matches' + bmpEscape.matches') +
      highEscape.matches' * lowEscape.matches' ≤
      (unescaped.matches' + shortEscape.matches' + unitEscape.matches')∗
  refine sup_le (sup_le (le_trans ?_ le_kstar) (le_trans ?_ le_kstar)) ?_
  · exact le_sup_left
  · exact le_sup_of_le_right bmpEscape_le
  · refine le_trans ?_ (mul_kstar_le_kstar (a := _))
    refine le_trans (mul_le_mul' (le_sup_of_le_right highEscape_le) ?_) le_rfl
    exact le_trans (le_sup_of_le_right lowEscape_le) le_kstar

theorem string_le : (string .scalarEscapes).matches' ≤ (string .rfc8259).matches' := by
  show (char 0x22).matches' * (strChar .scalarEscapes).matches'∗ * (char 0x22).matches' ≤
    (char 0x22).matches' * (strChar .rfc8259).matches'∗ * (char 0x22).matches'
  exact mul_le_mul' (mul_le_mul' le_rfl ((kstar_mono strChar_le).trans (kstar_idem _).le)) le_rfl

theorem scalar_le : (scalar .scalarEscapes).matches' ≤ (scalar .rfc8259).matches' := by
  show falseLit.matches' + nullLit.matches' + trueLit.matches' + number.matches' +
      (string .scalarEscapes).matches' ≤ falseLit.matches' + nullLit.matches' +
      trueLit.matches' + number.matches' + (string .rfc8259).matches'
  gcongr
  exact string_le

mutual

theorem value_rfc8259 {w : List UInt8} : Value .scalarEscapes w → Value .rfc8259 w
  | .scalar h => .scalar (scalar_le h)
  | .emptyArray ha hb => .emptyArray ha hb
  | .array ha hx hb => .array ha (elements_rfc8259 hx) hb
  | .emptyObject ha hb => .emptyObject ha hb
  | .object ha hm hb => .object ha (members_rfc8259 hm) hb

theorem elements_rfc8259 {w : List UInt8} : Elements .scalarEscapes w → Elements .rfc8259 w
  | .one hv => .one (value_rfc8259 hv)
  | .cons hv hs hx => .cons (value_rfc8259 hv) hs (elements_rfc8259 hx)

theorem members_rfc8259 {w : List UInt8} : Members .scalarEscapes w → Members .rfc8259 w
  | .one hk hc hv => .one (string_le hk) hc (value_rfc8259 hv)
  | .cons hk hc hv hs hm =>
    .cons (string_le hk) hc (value_rfc8259 hv) hs (members_rfc8259 hm)

end

theorem language_le : language .scalarEscapes ≤ language .rfc8259 := by
  rintro w ⟨a, v, b, ha, hv, hb, rfl⟩
  exact ⟨a, v, b, ha, value_rfc8259 hv, hb, rfl⟩

end Silmaril.Proofs.Formats.JsonBytes.Profile

end
