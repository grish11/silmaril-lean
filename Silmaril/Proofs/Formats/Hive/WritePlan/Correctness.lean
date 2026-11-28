module

public import Silmaril.Formats.Hive.WritePlan.Defs

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Hive.WritePlan
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

private theorem groupRows_eq_referenceGroups (classified : List (String × Scan.Row physical Value)) :
    groupRows classified = referenceGroups classified := by
  induction classified using groupRows.induct with
  | case1 => simp [groupRows, referenceGroups]
  | case2 directory row rest groups ih =>
    dsimp only [groups] at ih
    rw [groupRows]
    simp only [List.partition_eq_filter_filter, Function.comp_def] at ih ⊢
    rw [ih]
    simp only [referenceGroups, List.map_cons, List.eraseDups_cons, List.filter_map, Function.comp_def]
    congr 1
    · simp
    · apply List.map_congr_left
      intro other member
      have distinct : other ≠ directory := by
        have kept := List.mem_eraseDups.mp member
        have found := List.mem_map.mp kept
        obtain ⟨entry, included, rfl⟩ := found
        simpa using (List.mem_filter.mp included).2
      congr 1
      simp only [List.filter_cons, beq_eq_false_iff_ne.mpr distinct.symm, Bool.false_eq_true, ↓reduceIte,
        List.filter_filter]
      congr 1
      apply List.filter_congr
      intro entry _
      by_cases hit : entry.1 = other
      · simp [hit, distinct]
      · simp [hit]

theorem plan_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) :
    plan physical schema options encode rows = reference physical schema options encode rows := by
  unfold plan reference
  split
  · rfl
  · cases classified : classify options encode rows with
    | error reason => rfl
    | ok entries => exact congrArg Except.ok (groupRows_eq_referenceGroups entries)

private theorem classify_cons (options : PartitionPath.Options) (encode : Encode Value Failure)
    (row : Scan.Row (schema.extend physical) Value) (rest : Scan.Table (schema.extend physical) Value)
    (offset : Nat) :
    classify options encode (row :: rest) offset =
      match classifyRow options encode row with
      | .error reason => .error (.row offset reason)
      | .ok entry => (classify options encode rest (offset + 1)).map (entry :: ·) := by
  unfold classify
  rw [List.zipIdx_cons, List.mapM_cons]
  cases classifyRow options encode row <;> rfl

private theorem classifyRows_first_error_iff (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) (offset index : Nat) (reason : RowError Failure) :
    classify options encode rows offset = .error (.row index reason) ↔
    ∃ before row after,
      rows = before ++ row :: after ∧ index = offset + before.length ∧
      (∀ prior ∈ before, ∃ entry, classifyRow options encode prior = .ok entry) ∧
      classifyRow options encode row = .error reason := by
  induction rows generalizing offset with
  | nil => simp [classify, pure, Except.pure]
  | cons row rest ih =>
    rw [classify_cons]
    cases checked : classifyRow options encode row with
    | error first =>
      simp only [Except.error.injEq, Error.row.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨[], row, rest, rfl, by simp, by simp, checked⟩
      · rintro ⟨before, failedRow, after, split, atIndex, earlier, failed⟩
        cases before with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          exact ⟨by simpa using atIndex.symm, Except.error.inj (checked.symm.trans failed)⟩
        | cons firstRow before =>
          have same : row = firstRow := (List.cons.inj split).1
          obtain ⟨entry, admitted⟩ := earlier firstRow (List.mem_cons_self ..)
          rw [← same, checked] at admitted
          cases admitted
    | ok entry =>
      have tailError :
          (classify options encode rest (offset + 1)).map (entry :: ·) = .error (.row index reason) ↔
          classify options encode rest (offset + 1) = .error (.row index reason) := by
        cases classify options encode rest (offset + 1) <;> simp [Except.map]
      rw [tailError, ih]
      constructor
      · rintro ⟨before, failedRow, after, rfl, atIndex, earlier, failed⟩
        refine ⟨row :: before, failedRow, after, rfl, ?_, ?_, failed⟩
        · simp only [List.length_cons] at atIndex ⊢
          omega
        · intro prior member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨entry, checked⟩
          · exact earlier prior member
      · rintro ⟨before, failedRow, after, split, atIndex, earlier, failed⟩
        cases before with
        | nil =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj split
          rw [checked] at failed
          cases failed
        | cons firstRow before =>
          obtain ⟨rfl, tail⟩ := List.cons.inj split
          refine ⟨before, failedRow, after, tail, ?_, ?_, failed⟩
          · simp only [List.length_cons] at atIndex ⊢
            omega
          · exact fun prior member => earlier prior (List.mem_cons_of_mem _ member)

theorem plan_first_row_error_iff (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) (index : Nat) (reason : RowError Failure) :
    plan physical schema options encode rows = .error (.row index reason) ↔
    TypedPartitions.checkSchema (Failure := Failure) physical schema = .ok () ∧
      ∃ before row after,
        rows = before ++ row :: after ∧ index = before.length ∧
        (∀ prior ∈ before, ∃ entry, classifyRow options encode prior = .ok entry) ∧
        classifyRow options encode row = .error reason := by
  cases checked : TypedPartitions.checkSchema (Failure := Failure) physical schema with
  | error error => simp [plan, checked]
  | ok accepted =>
    cases accepted
    simp only [plan, checked, true_and]
    have mapped : (classify options encode rows).map groupRows = .error (.row index reason) ↔
        classify options encode rows = .error (.row index reason) := by
      cases classify options encode rows <;> simp [Except.map]
    rw [mapped]
    simpa only [Nat.zero_add] using classifyRows_first_error_iff options encode rows 0 index reason

end Silmaril.Proofs.Formats.Hive.WritePlan
