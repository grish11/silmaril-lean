module

public import Silmaril.Courses.Cambridge.L3.Concrete.Fields

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete

open Silmaril.Courses.Cambridge.Concrete

variable {α β : Type}

theorem recordEntries_map (labels : RecordLabels) (fields : labels.Index → α) (f : α → β) :
    (recordEntries labels fields).map (fun (label, value) => (label, f value)) =
      recordEntries labels (fun i => f (fields i)) := by
  simp [RecordLabels.entries, List.map_ofFn, Function.comp_def]

theorem mem_recordEntries {labels : RecordLabels} {fields : labels.Index → α} {entry : Label × α} :
    entry ∈ recordEntries labels fields ↔ ∃ i, (labels.label i, fields i) = entry :=
  List.mem_ofFn

theorem recordEntries_labels (labels : RecordLabels) (fields : labels.Index → α) :
    (recordEntries labels fields).map Prod.fst = labels.names :=
  RecordLabels.entries_labels labels fields

theorem buildFields_recordEntries (labels : RecordLabels) (fields : labels.Index → α) :
    buildFields (recordEntries labels fields) = some ⟨labels, fields⟩ :=
  RecordLabels.ofEntries_entries labels fields

private theorem fieldsTokens_cons_cons (separator : Punct) (label : Label)
    (value : List Token) (next : Label × List Token) (rest : List (Label × List Token)) :
    fieldsTokens separator ((label, value) :: next :: rest) =
      .variable label :: .punct separator :: (value ++ .punct .comma :: fieldsTokens separator (next :: rest)) :=
  rfl

theorem fields_length (separator : Punct) (entries : List (Label × List Token)) :
    entries.length ≤ (fieldsTokens separator entries).length := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    rcases entry with ⟨label, value⟩
    cases entries <;> simp [fieldsTokens] at *; omega

theorem field_length (separator : Punct) {entries : List (Label × List Token)}
    {entry : Label × List Token} (h : entry ∈ entries) :
    entry.2.length ≤ (fieldsTokens separator entries).length := by
  induction entries with
  | nil => contradiction
  | cons first rest ih =>
    rcases first with ⟨label, value⟩
    rcases List.mem_cons.mp h with rfl | hm
    · cases rest <;> simp [fieldsTokens] <;> omega
    · have hrest := ih hm
      cases rest with
      | nil => contradiction
      | cons next rest =>
        rw [fieldsTokens_cons_cons]
        simp only [List.length_cons, List.length_append]
        omega

private theorem readFields_print (read : List Token → Option (α × List Token))
    (write : α → List Token) (separator : Punct) (entries : List (Label × α))
    (fuel : Nat) (suffix : List Token) (hn : entries ≠ []) (h : entries.length ≤ fuel)
    (hread : ∀ entry ∈ entries, ∀ tail, read (write entry.2 ++ tail) = some (entry.2, tail)) :
    readFields read separator fuel
      (fieldsTokens separator (entries.map (fun (name, value) => (name, write value))) ++ suffix) =
      some (entries, suffix) := by
  induction entries generalizing fuel with
  | nil => exact (hn rfl).elim
  | cons first rest ih =>
    rcases first with ⟨label, value⟩
    have hv := hread (label, value) (by simp)
    have hr : ∀ entry ∈ rest, ∀ tail, read (write entry.2 ++ tail) = some (entry.2, tail) :=
      fun entry he => hread entry (List.mem_cons_of_mem _ he)
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      cases rest with
      | nil => simp [fieldsTokens, readFields, expect, List.append_assoc, hv]
      | cons next rest =>
        have bound : (next :: rest).length ≤ fuel := Nat.le_of_succ_le_succ h
        have row :
            fieldsTokens separator (((label, value) :: next :: rest).map
              (fun (name, value) => (name, write value))) =
            .variable label :: .punct separator ::
              (write value ++ .punct .comma :: fieldsTokens separator
                ((next :: rest).map (fun (name, value) => (name, write value)))) := rfl
        have parsedTail := ih fuel (by simp) bound hr
        simp only [List.map_cons] at parsedTail
        rw [row]
        simp [List.append_assoc, readFields, expect, hv, parsedTail]

theorem readRecord_print (make : (labels : RecordLabels) → (labels.Index → α) → α)
    (read : List Token → Option (α × List Token)) (write : α → List Token)
    (separator : Punct) (labels : RecordLabels) (fields : labels.Index → α)
    (fuel : Nat) (suffix : List Token)
    (h : (recordEntries labels fields).length ≤ fuel)
    (hread : ∀ i tail, read (write (fields i) ++ tail) = some (fields i, tail)) :
    readRecord make read separator fuel
      (fieldsTokens separator (recordEntries labels (fun i => write (fields i))) ++ suffix) =
      some (make labels fields, suffix) := by
  rw [← recordEntries_map labels fields write]
  have hr : ∀ entry ∈ recordEntries labels fields, ∀ tail,
      read (write entry.2 ++ tail) = some (entry.2, tail) := by
    intro entry he
    obtain ⟨i, rfl⟩ := mem_recordEntries.mp he
    exact hread i
  have hb := buildFields_recordEntries labels fields
  cases hs : recordEntries labels fields with
  | nil =>
    rw [hs] at hb
    simp [readRecord, readFieldList, fieldsTokens, hb]
  | cons first rest =>
    have hp := readFields_print read write separator (first :: rest) fuel suffix (by simp)
      (hs ▸ h) (hs ▸ hr)
    obtain ⟨name, value⟩ := first
    unfold readRecord
    have parsed : readFieldList read separator fuel
        (fieldsTokens separator (((name, value) :: rest).map
          (fun (name, value) => (name, write value))) ++ suffix) =
        some ((name, value) :: rest, suffix) := hp
    rw [parsed]
    change (buildFields ((name, value) :: rest)).bind _ = _
    rw [hs] at hb
    rw [hb]
    rfl

theorem readRecord_print_bounded (make : (labels : RecordLabels) → (labels.Index → α) → α)
    (read : List Token → Option (α × List Token)) (write : α → List Token)
    (separator : Punct) (labels : RecordLabels) (fields : labels.Index → α)
    (fuel : Nat) (suffix : List Token)
    (h : (fieldsTokens separator (recordEntries labels (fun i => write (fields i)))).length ≤ fuel)
    (hread : ∀ i tail, (write (fields i)).length ≤ fuel →
      read (write (fields i) ++ tail) = some (fields i, tail)) :
    readRecord make read separator fuel
      (fieldsTokens separator (recordEntries labels (fun i => write (fields i))) ++ suffix) =
      some (make labels fields, suffix) := by
  apply readRecord_print
  · have count := fields_length separator (recordEntries labels (fun i => write (fields i)))
    simpa only [recordEntries, RecordLabels.entries, List.length_ofFn] using (Nat.le_trans count h)
  · intro i tail
    apply hread
    apply Nat.le_trans _ h
    have member : (labels.label i, write (fields i)) ∈
        recordEntries labels (fun j => write (fields j)) := mem_recordEntries.mpr ⟨i, rfl⟩
    exact field_length separator member

def TokensSpelled (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, Spellable token

@[simp] theorem tokensSpelled_nil : TokensSpelled [] := List.forall_mem_nil _

@[simp] theorem tokensSpelled_cons {token : Token} {tokens : List Token} :
    TokensSpelled (token :: tokens) ↔ Spellable token ∧ TokensSpelled tokens :=
  List.forall_mem_cons

@[simp] theorem tokensSpelled_append {left right : List Token} :
    TokensSpelled (left ++ right) ↔ TokensSpelled left ∧ TokensSpelled right :=
  List.forall_mem_append

theorem fieldsTokens_spelled (separator : Punct) (entries : List (Label × List Token))
    (h : ∀ entry ∈ entries, IsName entry.1 ∧ TokensSpelled entry.2) :
    TokensSpelled (fieldsTokens separator entries) := by
  induction entries with
  | nil => simp [fieldsTokens]
  | cons entry rest ih =>
    rcases entry with ⟨name, value⟩
    obtain ⟨hn, hv⟩ := h (name, value) (by simp)
    have hr := ih (fun entry he => h entry (List.mem_cons_of_mem _ he))
    cases rest with
    | nil => simp [fieldsTokens, hn, hv]
    | cons next rest =>
      rw [fieldsTokens_cons_cons]
      simp [hn, hv, hr]

theorem recordTokens_spelled (separator : Punct) (labels : RecordLabels)
    (fields : labels.Index → List Token)
    (h : ∀ i, IsName (labels.label i) ∧ TokensSpelled (fields i)) :
    TokensSpelled (fieldsTokens separator (recordEntries labels fields)) := by
  apply fieldsTokens_spelled
  intro entry hm
  obtain ⟨i, rfl⟩ := mem_recordEntries.mp hm
  exact h i

end Silmaril.Courses.Cambridge.L3.Concrete
