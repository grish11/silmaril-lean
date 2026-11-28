module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Proofs

open CategoryTheory
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct_id reduct_comp)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

set_option backward.isDefEq.respectTransparency false

variable {P Q R : EntrySignature} {args : List ValueSort} {cells : Nat}

theorem decodePayload_encode (entry : Entry args cells) :
    decodePayload (encodeInput entry.heap entry.input) = entry := by
  obtain ⟨input, heap⟩ := entry
  induction input with
  | nil => rfl
  | cons value tail ih =>
    change Entry.mk (.cons value (decodePayload (encodeInput heap tail)).input)
      (decodePayload (encodeInput heap tail)).heap = _
    rw [ih]

theorem encode_decodePayload (payload : Tuple (WireVal cells) (carrier args)) :
    encodeInput (decodePayload payload).heap (decodePayload payload).input = payload := by
  induction args with
  | nil =>
    cases payload with
    | cons heap rest => cases rest; rfl
  | cons _ _ ih =>
    cases payload with
    | cons value rest =>
      change Tuple.cons value (encodeInput (decodePayload rest).heap (decodePayload rest).input) = _
      rw [ih rest]

theorem decode_encode (entry : Entry args cells) : decode entry.encode = some entry := by
  change some (decodePayload (encodeInput entry.heap entry.input)) = some entry
  rw [decodePayload_encode]

theorem decode_eq_some_iff (raw : RawEntry args cells) (entry : Entry args cells) :
    decode raw = some entry ↔ entry.encode = raw := by
  constructor
  · cases raw with
    | cons tag payload =>
      intro decoded
      by_cases entered : tag.down = 0
      · have data : decodePayload payload = entry :=
          Option.some.inj (by simpa only [decode, ite_eq_left entered] using decoded)
        have colour : tag = Petri.arrivalColour .entry := congrArg ULift.up entered
        change Tuple.cons (F := WireVal cells) (t := .control 2) (Petri.arrivalColour .entry)
          (encodeInput entry.heap entry.input) = Tuple.cons tag payload
        rw [← colour, ← data, encode_decodePayload]
      · simp [decode, entered] at decoded
  · rintro rfl
    exact decode_encode entry

theorem decode_eq_none_iff (raw : RawEntry args cells) : decode raw = none ↔ ¬ Admissible raw := by
  cases raw with
  | cons tag payload =>
    change (if tag.down = 0 then some (decodePayload payload) else none) = none ↔ ¬ tag.down = 0
    by_cases entered : tag.down = 0 <;> simp [entered]

theorem admissible_iff_exists_encode (raw : RawEntry args cells) :
    Admissible raw ↔ ∃ entry : Entry args cells, entry.encode = raw := by
  constructor
  · cases raw with
    | cons tag payload =>
      intro entered
      have isZero : tag.down = 0 := entered
      exact ⟨decodePayload payload, (decode_eq_some_iff _ _).mp (by simp only [decode, ite_eq_left isZero])⟩
  · rintro ⟨entry, rfl⟩
    rfl

theorem reindex_encode (h : P ⟶ Q) (entry : Entry Q.args cells) :
    reindex h entry.encode = (entry.reduct h).encode := by
  change Tuple.cons (F := WireVal cells) (t := .control 2) (Petri.arrivalColour .entry)
    (encodeInput ((decodePayload (encodeInput entry.heap entry.input)).reduct h).heap
      ((decodePayload (encodeInput entry.heap entry.input)).reduct h).input) = _
  rw [decodePayload_encode]
  rfl

theorem decode_reindex (h : P ⟶ Q) (raw : RawEntry Q.args cells) :
    decode (reindex h raw) = (decode raw).map (Entry.reduct h) := by
  cases raw with
  | cons tag payload =>
    let pulled := (decodePayload payload).reduct h
    change (if tag.down = 0 then some (decodePayload (encodeInput pulled.heap pulled.input)) else none) =
      (if tag.down = 0 then some (decodePayload payload) else none).map (Entry.reduct h)
    rw [decodePayload_encode]
    split <;> rfl

private theorem eq_of_model_and_heap {left right : Entry P.args cells}
    (models : left.model (P := P) = right.model (P := P)) (heaps : left.heap = right.heap) :
    left = right := by
  cases left with
  | mk leftInput leftHeap =>
    cases right with
    | mk rightInput rightHeap =>
      change EntryModel.mk cells leftInput = EntryModel.mk cells rightInput at models
      simp only [Entry.mk.injEq]
      exact ⟨eq_of_heq (EntryModel.mk.inj models).2, heaps⟩

private theorem entry_reduct_id (entry : Entry P.args cells) :
    entry.reduct (𝟙 P) = entry :=
  eq_of_model_and_heap (P := P) (reduct_id entry.model) rfl

private theorem entry_reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (entry : Entry R.args cells) :
    entry.reduct (h ≫ k) = (entry.reduct k).reduct h :=
  eq_of_model_and_heap (P := P) (reduct_comp h k entry.model) rfl

theorem reindex_id (raw : RawEntry P.args cells) : reindex (𝟙 P) raw = raw := by
  cases raw with
  | cons tag payload =>
    simp only [reindex, entry_reduct_id, encode_decodePayload]

theorem reindex_comp (h : P ⟶ Q) (k : Q ⟶ R) (raw : RawEntry R.args cells) :
    reindex (h ≫ k) raw = reindex h (reindex k raw) := by
  cases raw with
  | cons tag payload =>
    simp only [reindex, entry_reduct_comp, decodePayload_encode]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Proofs
