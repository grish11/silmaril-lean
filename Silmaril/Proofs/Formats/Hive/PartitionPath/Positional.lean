module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Defs

public section

namespace Silmaril.Proofs.Formats.Hive.PartitionPath.Positional

open Silmaril.Formats.Hive.PartitionPath
open Silmaril.Formats.Hive.PartitionPath.Positional

theorem parseSegments_ok_iff (keys : List String) (encoding : Encoding)
    (options : Options) (raw : List String) (entries : Partition) :
    parseSegments keys encoding options raw = .ok entries ↔
      raw.length = keys.length ∧
        ∃ values, raw.mapM (decodeSegment encoding) = .ok values ∧
          entries = keys.zip (values.map some) ∧ validate options entries = .ok () := by
  by_cases arity : raw.length = keys.length
  · cases decoded : raw.mapM (decodeSegment encoding) with
    | error reason => simp [parseSegments, arity, decoded, Except.bind]
    | ok values =>
      have rhs :
          (raw.length = keys.length ∧
            ∃ out, (Except.ok values : Except Error (List String)) = .ok out ∧
              entries = keys.zip (out.map some) ∧ validate options entries = .ok ()) ↔
            entries = keys.zip (values.map some) ∧ validate options (keys.zip (values.map some)) = .ok () := by
        simp only [arity, Except.ok.injEq, true_and]
        constructor
        · rintro ⟨out, rfl, rfl, valid⟩
          exact ⟨rfl, valid⟩
        · rintro ⟨rfl, valid⟩
          exact ⟨values, rfl, rfl, valid⟩
      rw [rhs]
      cases checked : validate options (keys.zip (values.map some)) with
      | error reason => simp [parseSegments, arity, decoded, checked, Except.bind, Except.map]
      | ok valid =>
        cases valid
        simp [parseSegments, arity, decoded, checked, Except.bind, Except.map, eq_comm]
  · simp [parseSegments, arity]

theorem parse_ok_iff (maxDirectoryBytes : Nat) (keys : List String) (encoding : Encoding)
    (options : Options) (directory : String) (entries : Partition) :
    Positional.parse maxDirectoryBytes keys encoding options directory = .ok entries ↔
      directory.utf8ByteSize ≤ maxDirectoryBytes ∧ (segments directory).length = keys.length ∧
        ∃ values, (segments directory).mapM (decodeSegment encoding) = .ok values ∧
          entries = keys.zip (values.map some) ∧ validate options entries = .ok () := by
  by_cases size : directory.utf8ByteSize ≤ maxDirectoryBytes
  · simp [Positional.parse, Nat.not_lt.mpr size, size, parseSegments_ok_iff]
  · simp [Positional.parse, Nat.lt_of_not_ge size, size]

private theorem length_of_mapM {α β ε : Type} (check : α → Except ε β)
    {input : List α} {output : List β} (success : input.mapM check = .ok output) :
    output.length = input.length := by
  induction input generalizing output with
  | nil =>
    change Except.ok [] = Except.ok output at success
    cases success
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at success
    cases first : check head with
    | error reason => simp [first, bind, Except.bind] at success
    | ok value =>
      cases rest : tail.mapM check with
      | error reason => simp [first, rest, bind, Except.bind] at success
      | ok values =>
        simp [first, rest, bind, Except.bind, pure, Except.pure] at success
        subst output
        simp [ih rest]

private theorem zip_present (keys values : List String) :
    ∀ entry ∈ keys.zip (values.map some), (entry : Entry).2.isSome = true := by
  induction keys generalizing values with
  | nil => simp
  | cons key rest ih =>
    cases values with
    | nil => simp
    | cons value tail =>
      intro entry member
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih tail entry member

theorem parseSegments_keys_present {keys : List String} {encoding : Encoding}
    {options : Options} {raw : List String} {entries : Partition}
    (parsed : parseSegments keys encoding options raw = .ok entries) :
    entries.map Prod.fst = keys ∧ ∀ entry ∈ entries, entry.2.isSome = true := by
  obtain ⟨arity, values, decoded, rfl, _⟩ := (parseSegments_ok_iff _ _ _ _ _).mp parsed
  have sizes : keys.length ≤ (values.map some).length := by
    simp only [List.length_map, length_of_mapM _ decoded, arity, Nat.le_refl]
  exact ⟨List.map_fst_zip sizes, zip_present keys values⟩

theorem parse_keys_present {maxDirectoryBytes : Nat} {keys : List String} {encoding : Encoding}
    {options : Options} {directory : String} {entries : Partition}
    (parsed : Positional.parse maxDirectoryBytes keys encoding options directory = .ok entries) :
    entries.map Prod.fst = keys ∧ ∀ entry ∈ entries, entry.2.isSome = true :=
  parseSegments_keys_present ((parseSegments_ok_iff _ _ _ _ _).mpr ((parse_ok_iff _ _ _ _ _ _).mp parsed).2)

end Silmaril.Proofs.Formats.Hive.PartitionPath.Positional
