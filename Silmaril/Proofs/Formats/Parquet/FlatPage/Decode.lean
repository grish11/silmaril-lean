module

public import Silmaril.Formats.Parquet.FlatPage.Defs
import Silmaril.Proofs.Formats.Parquet.FlatPage.Levels
import Silmaril.Proofs.Formats.Parquet.FlatPage.Reconstruct

namespace Silmaril.Proofs.Formats.Parquet.FlatPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatPage

public theorem plan_sound {schema : LevelSchema} {slots present : Nat} {limits : Hybrid.Limits}
    {body : Body} {checked : Plan} (h : plan schema slots present limits body = .ok checked) :
    ∃ layout sections, schema.layout? = some layout ∧
      split layout limits.bytes body = .ok sections ∧
      readMask layout slots limits sections.definitions = .ok checked.mask ∧
      checked.scalars = sections.scalars ∧ checked.mask.count true = present := by
  cases hs : schema.layout? with
  | none => simp [plan, hs, throw] at h
  | some layout =>
    by_cases overflow : slots < present
    · simp [plan, hs, overflow, throw] at h
    · cases hb : split layout limits.bytes body with
      | error e => simp [plan, hs, overflow, hb, bind, Except.bind] at h
      | ok sections =>
        cases hm : readMask layout slots limits sections.definitions with
        | error e => simp [plan, hs, overflow, hb, hm, bind, Except.bind] at h
        | ok mask =>
          by_cases count : mask.count true = present
          · simp [plan, hs, overflow, hb, hm, count, bind, Except.bind, pure, Except.pure] at h
            cases h
            exact ⟨layout, sections, rfl, hb, hm, rfl, count⟩
          · simp [plan, hs, overflow, hb, hm, count, bind, Except.bind, throw] at h

public theorem decode_ok_iff {α ε : Type} {schema : LevelSchema} {slots present : Nat}
    {limits : Hybrid.Limits} {body : Body} {scalar : Nat → Bytes → Except ε (List α)}
    {output : List (Option α)} :
    decode schema slots present limits body scalar = .ok output ↔
      ∃ checked values, plan schema slots present limits body = .ok checked ∧
        scalar present checked.scalars = .ok values ∧
        output.map Option.isSome = checked.mask ∧ output.filterMap id = values := by
  constructor
  · intro h
    cases hp : plan schema slots present limits body with
    | error e => simp [decode, hp] at h
    | ok checked =>
      cases hs : scalar present checked.scalars with
      | error e => simp [decode, hp, hs] at h
      | ok values =>
        cases hr : reconstruct checked.mask values with
        | error e => simp [decode, hp, hs, hr] at h
        | ok out =>
          simp [decode, hp, hs, hr] at h
          subst out
          exact ⟨checked, values, rfl, hs, reconstruct_ok_iff.mp hr⟩
  · rintro ⟨checked, values, hp, hs, shape, order⟩
    simp [decode, hp, hs, reconstruct_ok_iff.mpr ⟨shape, order⟩]

public theorem decode_counts {α ε : Type} {schema : LevelSchema} {slots present : Nat}
    {limits : Hybrid.Limits} {body : Body} {scalar : Nat → Bytes → Except ε (List α)}
    {output : List (Option α)} (h : decode schema slots present limits body scalar = .ok output) :
    output.length = slots ∧ (output.filterMap id).length = present := by
  obtain ⟨checked, values, hp, _, shape, _⟩ := decode_ok_iff.mp h
  obtain ⟨_, _, _, _, hm, _, hcount⟩ := plan_sound hp
  refine ⟨?_, ?_⟩
  · have lengths := congrArg List.length shape
    rw [List.length_map, readMask_length hm] at lengths
    exact lengths
  · rw [← present_count_eq output, shape, hcount]

public theorem decode_exists_iff {α ε : Type} (schema : LevelSchema) (slots present : Nat)
    (limits : Hybrid.Limits) (body : Body) (scalar : Nat → Bytes → Except ε (List α)) :
    (∃ output, decode schema slots present limits body scalar = .ok output) ↔
      ∃ checked values, plan schema slots present limits body = .ok checked ∧
        scalar present checked.scalars = .ok values ∧ values.length = present := by
  constructor
  · rintro ⟨output, h⟩
    obtain ⟨checked, values, hp, hs, _, order⟩ := decode_ok_iff.mp h
    exact ⟨checked, values, hp, hs, order ▸ (decode_counts h).2⟩
  · rintro ⟨checked, values, hp, hs, size⟩
    obtain ⟨_, _, _, _, _, _, count⟩ := plan_sound hp
    obtain ⟨output, reconstructed⟩ := (reconstruct_exists_iff checked.mask values).mpr
      (count.trans size.symm)
    obtain ⟨shape, order⟩ := reconstruct_ok_iff.mp reconstructed
    exact ⟨output, decode_ok_iff.mpr ⟨checked, values, hp, hs, shape, order⟩⟩

end Silmaril.Proofs.Formats.Parquet.FlatPage
