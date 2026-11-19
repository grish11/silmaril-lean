module

public import Silmaril.Wasm.Region.ByteMap.Nested.Examples.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Nested.Examples

set_option maxRecDepth 10000

theorem nested_body : nested.BodyChecks := by decide +kernel
theorem conditional_body : conditional.BodyChecks := by decide +kernel
theorem handler_body : handler.BodyChecks := by decide +kernel
theorem prefixed_body : prefixed.BodyChecks := by decide +kernel

theorem nested_table : TableChecks nested nestedTable := by decide +kernel
theorem conditional_table : TableChecks conditional conditionalTable := by decide +kernel
theorem handler_table : TableChecks handler handlerTable := by decide +kernel
theorem prefixed_table : TableChecks prefixed prefixedTable := by decide +kernel

def nestedCertified := certify nested nestedTable nested_body nested_table
def conditionalCertified := certify conditional conditionalTable conditional_body conditional_table
def handlerCertified := certify handler handlerTable handler_body handler_table
def prefixedCertified := certify prefixed prefixedTable prefixed_body prefixed_table

/-- Equal NOPs in opposite if arms cannot exchange their source locations. -/
theorem wrong_arm_offset_rejected :
    ¬ (Candidate.mk ⟨⟨8, [(0, 1)], 0⟩, r 3 4⟩ [arm 1]).Checks conditional := by decide +kernel

theorem header_shift_rejected :
    ¬ (Candidate.mk ⟨⟨7, [(0, 0), (0, 0)], 0⟩, r 4 5⟩ [outer, inner]).Checks nested := by decide +kernel

theorem wrong_segment_index_rejected :
    ¬ (Candidate.mk ⟨⟨10, [(1, 0)], 0⟩, r 4 5⟩
      [{ prefixedFrame with segmentIndex := 1 }]).Checks prefixed := by decide +kernel

theorem omitted_ancestry_rejected :
    ¬ (Candidate.mk ⟨⟨7, [(0, 0), (0, 0)], 0⟩, r 5 6⟩ [inner]).Checks nested := by decide +kernel

theorem delimiter_is_not_instruction :
    ¬ (Candidate.mk ⟨⟨7, [(0, 0), (0, 0)], 1⟩, r 6 7⟩ [outer, inner]).Checks nested := by decide +kernel

theorem function_mismatch_rejected :
    ¬ (Candidate.mk ⟨⟨8, [(0, 0), (0, 0)], 0⟩, r 5 6⟩ [outer, inner]).Checks nested := by decide +kernel

/-- Explicitly supplied inventory; completeness against a CFG inventory is a
separate client obligation, not inferred from successful table checking. -/
def nestedLabels : List DecodedLabel := [⟨7, [], 0⟩, ⟨7, [(0, 0)], 0⟩, ⟨7, [(0, 0), (0, 0)], 0⟩]

theorem nested_covered : Covered nestedLabels nestedTable := by decide

theorem nested_cfg_covered : Covered (inventory nested) nestedTable := by decide +kernel
theorem conditional_cfg_covered : Covered (inventory conditional) conditionalTable := by decide +kernel
theorem handler_cfg_covered : Covered (inventory handler) handlerTable := by decide +kernel
theorem prefixed_cfg_covered : Covered (inventory prefixed) prefixedTable := by decide +kernel

theorem nested_validated : validate? nested nestedTable = some nestedCertified :=
  validate_certify nested_body nested_table

/-- A correct partial map can be empty; acceptance does not establish coverage. -/
theorem empty_table_accepted : (validate? nested []).isSome = true := by decide +kernel

theorem empty_table_not_covering : ¬ Covered (inventory nested) [] := by decide +kernel

/-- The public validator rejects the swapped identical-arm occurrence too. -/
theorem wrong_arm_table_rejected :
    validate? conditional [⟨⟨⟨8, [(0, 1)], 0⟩, r 3 4⟩, [arm 1]⟩] = none := by decide +kernel

theorem nested_instruction_sound : DecodesAt nested ⟨7, [(0, 0), (0, 0)], 0⟩ (r 5 6) :=
  candidate_sound (candidate := ⟨⟨⟨7, [(0, 0), (0, 0)], 0⟩, r 5 6⟩, [outer, inner]⟩)
    nested_body (nested_table.1 _ (by simp [nestedTable]))

/-- The decoded empty else has no encoded else interval to invent a map for. -/
theorem absent_else_not_invented :
    ({ noElseFrame with arm := 1 } : Frame).child? (root noElse) = none := by decide

/-- Four accepted fixtures contain eleven listed instructions, including six
nested positions. This is a fixture denominator, not a module-corpus result. -/
theorem fixture_counts :
    nestedTable.length + conditionalTable.length + handlerTable.length + prefixedTable.length = 11 ∧
    ((nestedTable ++ conditionalTable ++ handlerTable ++ prefixedTable).filter
      (fun c => !c.entry.decoded.sequencePath.isEmpty)).length = 6 := by decide

end Silmaril.Wasm.Region.ByteMap.Nested.Examples
