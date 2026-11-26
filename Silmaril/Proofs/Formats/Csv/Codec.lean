module

public import Silmaril.Formats.Csv.Defs

/-! Proofs for `Silmaril.Formats.Csv.Thms`. -/

public section

namespace Silmaril.Proofs.Formats.Csv

open Silmaril.Formats.Csv
open Silmaril.Formats.Csv.Internal

private theorem readQuoted_sound {input : Bytes} {p : ParsedField input}
    (h : readQuoted input = some p) :
    p.field.all fieldData = true ∧ input = escape p.field ++ quote :: p.rest := by
  induction lengthEq : input.length using Nat.strongRecOn generalizing input with
  | ind length ih =>
    rw [readQuoted.eq_def] at h
    cases input with
    | nil => simp at h
    | cons b bs =>
      by_cases hb : b = quote
      · subst b
        cases bs with
        | nil =>
          simp at h
          subst p
          simp [escape]
        | cons c cs =>
          by_cases hc : c = quote
          · subst c
            cases hr : readQuoted cs with
            | none => simp [hr] at h
            | some q =>
              simp [hr] at h
              subst p
              have smaller : cs.length < length := by simp at lengthEq; omega
              obtain ⟨ok, shaped⟩ := ih cs.length smaller hr rfl
              exact ⟨by simp [fieldData, ok], by simpa [escape] using congrArg (quote :: quote :: ·) shaped⟩
          · simp [hc] at h
            subst p
            simp [escape]
      · by_cases ok : quotedData b = true
        · cases hr : readQuoted bs with
          | none => simp [hb, ok, hr] at h
          | some q =>
            simp [hb, ok, hr] at h
            subst p
            have smaller : bs.length < length := by simp at lengthEq; omega
            obtain ⟨fieldOk, shaped⟩ := ih bs.length smaller hr rfl
            exact ⟨by simp [fieldData, ok, fieldOk], by simpa [escape, hb] using congrArg (b :: ·) shaped⟩
        · simp [hb, ok] at h

private theorem readField_sound {input : Bytes} {p : ParsedField input}
    (h : readField input = some p) :
    ∃ wire, FieldWire wire p.field ∧ input = wire ++ p.rest := by
  cases input with
  | nil =>
    simp [readField] at h
    subst p
    exact ⟨[], .bare rfl, rfl⟩
  | cons b bs =>
    by_cases hb : b = quote
    · subst b
      cases hr : readQuoted bs with
      | none => simp [readField, hr] at h
      | some q =>
        simp [readField, hr] at h
        subst p
        obtain ⟨ok, shaped⟩ := readQuoted_sound hr
        exact ⟨_, .quoted ok, by simpa [quoteField, List.append_assoc] using congrArg (quote :: ·) shaped⟩
    · simp [readField, hb] at h
      subst p
      exact ⟨_, .bare List.all_takeWhile, List.takeWhile_append_dropWhile.symm⟩

/-- An empty suffix, or the head of a field or record delimiter. -/
private inductive Boundary : Bytes → Prop where
  | eof : Boundary []
  | comma (rest : Bytes) : Boundary (comma :: rest)
  | cr (rest : Bytes) : Boundary (cr :: rest)

private theorem Boundary.not_quote {tail : Bytes} (h : Boundary tail) :
    tail.head? ≠ some quote := by
  cases h
  · simp
  · simp only [List.head?_cons]; decide
  · simp only [List.head?_cons]; decide

private theorem Boundary.drop_bare {tail : Bytes} (h : Boundary tail) :
    tail.dropWhile textData = tail := by
  cases h
  · rfl
  · rw [List.dropWhile_cons_of_neg (by decide)]
  · rw [List.dropWhile_cons_of_neg (by decide)]

private theorem Boundary.take_bare {tail : Bytes} (h : Boundary tail) :
    tail.takeWhile textData = [] := by
  cases h
  · rfl
  · rw [List.takeWhile_cons_of_neg (by decide)]
  · rw [List.takeWhile_cons_of_neg (by decide)]

private theorem readQuoted_complete (field tail : Bytes) (ok : field.all fieldData = true)
    (boundary : tail.head? ≠ some quote) :
    ∃ p, readQuoted (escape field ++ quote :: tail) = some p ∧ p.field = field ∧ p.rest = tail := by
  induction field with
  | nil =>
    cases tail with
    | nil =>
      refine ⟨⟨[], [], by simp [escape]⟩, ?_, rfl, rfl⟩
      simp [escape, readQuoted]
    | cons b bs =>
      have hb : b ≠ quote := by simpa using boundary
      refine ⟨⟨[], b :: bs, by simp [escape]⟩, ?_, rfl, rfl⟩
      simp [escape, readQuoted, hb]
  | cons b bs ih =>
    have parts : fieldData b = true ∧ bs.all fieldData = true := by simpa only [List.all_cons, Bool.and_eq_true] using ok
    obtain ⟨p, hp, hpfield, hprest⟩ := ih parts.2
    by_cases hb : b = quote
    · subst b
      change ∃ q, readQuoted (quote :: quote :: (escape bs ++ quote :: tail)) = some q ∧
        q.field = quote :: bs ∧ q.rest = tail
      refine ⟨⟨quote :: p.field, p.rest, by have := p.rest_le; simp at *; omega⟩, ?_, ?_, hprest⟩
      · rw [readQuoted.eq_def]
        simp [hp]
      · exact congrArg (quote :: ·) hpfield
    · have hdata : quotedData b = true := by simpa [fieldData, hb] using parts.1
      have shaped : escape (b :: bs) ++ quote :: tail = b :: (escape bs ++ quote :: tail) := by
        rw [escape, ite_eq_right hb]; rfl
      rw [shaped]
      refine ⟨⟨b :: p.field, p.rest, by have := p.rest_le; simp at *; omega⟩, ?_, ?_, hprest⟩
      · rw [readQuoted.eq_def]
        simp [hb, hdata, hp]
      · exact congrArg (b :: ·) hpfield

private theorem readField_complete {wire field : Bytes} (h : FieldWire wire field)
    (tail : Bytes) (boundary : Boundary tail) :
    ∃ p, readField (wire ++ tail) = some p ∧ p.field = field ∧ p.rest = tail := by
  cases h with
  | bare ok =>
    have take : (wire ++ tail).takeWhile textData = wire := by
      rw [List.takeWhile_append_of_pos (List.all_eq_true.mp ok), boundary.take_bare, List.append_nil]
    have drop : (wire ++ tail).dropWhile textData = tail := by
      rw [List.dropWhile_append_of_pos (List.all_eq_true.mp ok), boundary.drop_bare]
    have head : (wire ++ tail).head? ≠ some quote := by
      cases wire with
      | nil => exact boundary.not_quote
      | cons b bs =>
        have hdata := List.all_eq_true.mp ok b List.mem_cons_self
        intro hq
        have hb : b = quote := by simpa using hq
        subst b
        exact (by decide : textData quote ≠ true) hdata
    generalize wire ++ tail = input at take drop head ⊢
    cases input with
    | nil => exact ⟨⟨[], [], Nat.le_refl _⟩, rfl, take, drop⟩
    | cons b bs =>
      have hb : b ≠ quote := by simpa using head
      refine ⟨⟨(b :: bs).takeWhile textData, (b :: bs).dropWhile textData,
        (List.dropWhile_sublist textData).length_le⟩, ?_, take, drop⟩
      simp only [readField.eq_def, ite_eq_right hb]
  | quoted ok =>
    obtain ⟨p, hp, hpfield, hprest⟩ := readQuoted_complete field tail ok boundary.not_quote
    have shaped : quoteField field ++ tail = quote :: (escape field ++ quote :: tail) := by
      simp [quoteField, List.append_assoc]
    rw [shaped]
    refine ⟨⟨p.field, p.rest, by have := p.rest_le; simp at *; omega⟩, ?_, hpfield, hprest⟩
    simp [readField, hp]

private theorem cr_ne_comma : cr ≠ comma := by decide

private theorem readRecords_sound {input : Bytes} {row : Row} {rows : Rows}
    (h : readRecords input = some (row, rows)) : Records input row rows := by
  induction lengthEq : input.length using Nat.strongRecOn generalizing input row rows with
  | ind length ih =>
    rw [readRecords.eq_def] at h
    cases hf : readField input with
    | none => simp [hf] at h
    | some p =>
      rcases p with ⟨value, tail, bound⟩
      obtain ⟨wire, field, shaped⟩ := readField_sound hf
      change FieldWire wire value at field
      change input = wire ++ tail at shaped
      rw [hf] at h
      cases tail with
      | nil =>
        obtain ⟨rfl, rfl⟩ : [value] = row ∧ rows = [] := by simpa using h
        rw [shaped, List.append_nil]
        exact .last field
      | cons b bs =>
        by_cases hc : b = comma
        · subst b
          cases hr : readRecords bs with
          | none => simp [hr] at h
          | some r =>
            obtain ⟨next, rest⟩ := r
            obtain ⟨rfl, rfl⟩ : value :: next = row ∧ rest = rows := by simpa [hr] using h
            have smaller : bs.length < length := by simp at bound; omega
            rw [shaped]
            exact .moreFields field (ih bs.length smaller hr rfl)
        · by_cases hcr : b = cr
          · subst b
            cases bs with
            | nil => simp [cr_ne_comma] at h
            | cons c rest =>
              by_cases hlf : c = lf
              · subst c
                cases rest with
                | nil =>
                  obtain ⟨rfl, rfl⟩ : [value] = row ∧ rows = [] := by simpa [cr_ne_comma] using h
                  rw [shaped]
                  exact .terminated field
                | cons d ds =>
                  cases hr : readRecords (d :: ds) with
                  | none => simp [cr_ne_comma, hr] at h
                  | some r =>
                    obtain ⟨next, later⟩ := r
                    obtain ⟨rfl, rfl⟩ : [value] = row ∧ next :: later = rows := by
                      simpa [cr_ne_comma, hr] using h
                    have smaller : (d :: ds).length < length := by simp at bound ⊢; omega
                    rw [shaped]
                    exact .moreRows field (by simp) (ih _ smaller hr rfl)
              · simp [cr_ne_comma, hlf] at h
          · simp [hc, hcr] at h

private theorem readRecords_complete {input : Bytes} {row : Row} {rows : Rows}
    (h : Records input row rows) : readRecords input = some (row, rows) := by
  induction h with
  | @last wire field spec =>
    suffices readRecords (wire ++ []) = some ([field], []) by simpa only [List.append_nil] using this
    obtain ⟨⟨value, tail, _⟩, hp, hf, ht⟩ := readField_complete spec [] .eof
    cases hf
    cases ht
    rw [readRecords.eq_def, hp]
    rfl
  | terminated field =>
    obtain ⟨⟨value, tail, _⟩, hp, hf, ht⟩ := readField_complete field [cr, lf] (.cr _)
    cases hf
    cases ht
    rw [readRecords.eq_def, hp]
    simp [cr_ne_comma]
  | @moreFields wire tail field row rows fieldWire _ ih =>
    obtain ⟨⟨value, rest, _⟩, hp, hf, hr⟩ := readField_complete fieldWire (comma :: tail) (.comma _)
    cases hf
    cases hr
    rw [readRecords.eq_def, hp]
    simp [ih]
  | @moreRows wire tail field row rows fieldWire nonempty _ ih =>
    cases tail with
    | nil => exact (nonempty rfl).elim
    | cons b bs =>
      obtain ⟨⟨value, rest, _⟩, hp, hf, hr⟩ := readField_complete fieldWire (cr :: lf :: b :: bs) (.cr _)
      cases hf
      cases hr
      rw [readRecords.eq_def, hp]
      simp [cr_ne_comma, ih]

theorem decode_eq_some_iff (input : Bytes) (rows : Rows) :
    decode input = some rows ↔ Parses input rows := by
  constructor
  · intro h
    cases input with
    | nil =>
      have : rows = [] := (Option.some.inj h).symm
      subst rows
      exact .empty
    | cons b bs =>
      cases hr : readRecords (b :: bs) with
      | none => simp [decode, hr] at h
      | some r =>
        obtain ⟨row, rest⟩ := r
        have : row :: rest = rows := by simpa [decode, hr] using h
        subst rows
        exact .records (by simp) (readRecords_sound hr)
  · intro h
    cases h with
    | empty => rfl
    | @records input row rows nonempty parsed =>
      cases input with
      | nil => exact (nonempty rfl).elim
      | cons b bs => simp [decode, readRecords_complete parsed]

private def RowWellFormed (row : Row) : Prop :=
  row ≠ [] ∧ ∀ field ∈ row, field.all fieldData = true

private theorem fieldWire_wellFormed {wire : Bytes} {field : Field} (h : FieldWire wire field) :
    field.all fieldData = true := by
  cases h with
  | bare ok =>
    apply List.all_eq_true.mpr
    intro b hb
    simp [fieldData, quotedData, List.all_eq_true.mp ok b hb]
  | quoted ok => exact ok

private theorem singletonRow_wellFormed {field : Field} (h : field.all fieldData = true) :
    RowWellFormed [field] := by
  refine ⟨by simp, ?_⟩
  intro f mem
  obtain rfl := List.mem_singleton.mp mem
  exact h

private theorem records_wellFormed {wire : Bytes} {row : Row} {rows : Rows}
    (h : Records wire row rows) : WellFormed (row :: rows) := by
  induction h with
  | last field | terminated field =>
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact singletonRow_wellFormed (fieldWire_wellFormed field)
  | @moreFields wire tail field row rows fieldWire _ ih =>
    have hrow := ih row List.mem_cons_self
    intro r mem
    rcases List.mem_cons.mp mem with rfl | mem
    · refine ⟨by simp, ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact fieldWire_wellFormed fieldWire
      · exact hrow.2 _ hf
    · exact ih r (List.mem_cons_of_mem _ mem)
  | @moreRows wire tail field row rows fieldWire _ _ ih =>
    intro r mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact singletonRow_wellFormed (fieldWire_wellFormed fieldWire)
    · exact ih r mem

theorem parses_wellFormed {wire : Bytes} {rows : Rows} (h : Parses wire rows) : WellFormed rows := by
  cases h with
  | empty => simp [WellFormed]
  | records _ spec => exact records_wellFormed spec

private theorem renderRow_records {row : Row} {tail : Bytes} {rows : Rows}
    (ok : RowWellFormed row) (next : Parses tail rows) : Records (renderRow row ++ tail) row rows := by
  induction row with
  | nil => exact (ok.1 rfl).elim
  | cons field fields ih =>
    have fieldOk : field.all fieldData = true := ok.2 field List.mem_cons_self
    cases fields with
    | nil =>
      cases next with
      | empty => simpa [renderRow] using Records.terminated (.quoted fieldOk)
      | records nonempty spec =>
        simpa [renderRow, List.append_assoc] using Records.moreRows (.quoted fieldOk) nonempty spec
    | cons f fs =>
      have restOk : RowWellFormed (f :: fs) :=
        ⟨by simp, fun field mem => ok.2 field (List.mem_cons_of_mem _ mem)⟩
      simpa [renderRow] using Records.moreFields (.quoted fieldOk) (ih restOk)

private theorem renderRow_ne_nil {row : Row} (h : row ≠ []) : renderRow row ≠ [] := by
  cases row with
  | nil => exact (h rfl).elim
  | cons field fields => cases fields <;> simp [renderRow, quoteField]

private theorem render_parses (rows : Rows) (h : WellFormed rows) : Parses (render rows) rows := by
  induction rows with
  | nil =>
    simpa only [render, List.flatMap_nil] using Parses.empty
  | cons row rows ih =>
    have hrow := h row List.mem_cons_self
    have hrows : WellFormed rows := fun r mem => h r (List.mem_cons_of_mem _ mem)
    rw [render, List.flatMap_cons]
    exact .records (by simp [renderRow_ne_nil hrow.1]) (renderRow_records hrow (ih hrows))

private theorem wellFormed_check (rows : Rows) :
    rows.all (fun row => !row.isEmpty && row.all (·.all fieldData)) = true ↔ WellFormed rows := by
  simp [WellFormed, List.all_eq_true, Bool.and_eq_true]

theorem encode_eq_none_iff (rows : Rows) : encode rows = none ↔ ¬ WellFormed rows := by
  unfold encode
  rw [← wellFormed_check]
  split
  next ok =>
    constructor
    · intro h
      cases h
    · exact fun h => (h ok).elim
  next bad => exact ⟨fun _ => bad, fun _ => rfl⟩

theorem encode_sound {rows : Rows} {wire : Bytes} (h : encode rows = some wire) : Parses wire rows := by
  unfold encode at h
  split at h
  next ok =>
    cases h
    exact render_parses rows ((wellFormed_check rows).mp ok)
  next => cases h

end Silmaril.Proofs.Formats.Csv
