module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Codec
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Observation
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms

/-! Entry validation, reindexing and equation truth for the emitted runtime. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry

open CategoryTheory
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature} {args : List ValueSort} {cells : Nat}

@[simp] theorem decodePayload_encode (entry : Entry args cells) :
    decodePayload (encodeInput entry.heap entry.input) = entry :=
  Proofs.decodePayload_encode entry

@[simp] theorem encode_decodePayload (payload : Tuple (WireVal cells) (carrier args)) :
    encodeInput (decodePayload payload).heap (decodePayload payload).input = payload :=
  Proofs.encode_decodePayload payload

@[simp] theorem admissible_encode (entry : Entry args cells) : Admissible entry.encode :=
  rfl

@[simp] theorem decode_encode (entry : Entry args cells) : decode entry.encode = some entry :=
  Proofs.decode_encode entry

/-- Successful validation recovers the exact typed input and all cells. -/
theorem decode_eq_some_iff (raw : RawEntry args cells) (entry : Entry args cells) :
    decode raw = some entry ↔ entry.encode = raw :=
  Proofs.decode_eq_some_iff raw entry

theorem decode_eq_none_iff (raw : RawEntry args cells) : decode raw = none ↔ ¬ Admissible raw :=
  Proofs.decode_eq_none_iff raw

/-- Raw entry colours and the image of the native encoding define the same domain. -/
theorem admissible_iff_exists_encode (raw : RawEntry args cells) :
    Admissible raw ↔ ∃ entry : Entry args cells, entry.encode = raw :=
  Proofs.admissible_iff_exists_encode raw

@[simp] theorem admissible_reindex (h : P ⟶ Q) (raw : RawEntry Q.args cells) :
    Admissible (reindex h raw) ↔ Admissible raw := by
  cases raw
  rfl

@[simp] theorem Entry.model_reduct (h : P ⟶ Q) (entry : Entry Q.args cells) :
    (entry.reduct h).model = Memory.Diamond.Institution.reduct h entry.model :=
  rfl

theorem reindex_encode (h : P ⟶ Q) (entry : Entry Q.args cells) :
    reindex h entry.encode = (entry.reduct h).encode :=
  Proofs.reindex_encode h entry

/-- Raw reindexing commutes with validation and the typed model reduct. -/
theorem decode_reindex (h : P ⟶ Q) (raw : RawEntry Q.args cells) :
    decode (reindex h raw) = (decode raw).map (Entry.reduct h) :=
  Proofs.decode_reindex h raw

@[simp] theorem reindex_id (raw : RawEntry P.args cells) : reindex (𝟙 P) raw = raw :=
  Proofs.reindex_id raw

theorem reindex_comp (h : P ⟶ Q) (k : Q ⟶ R) (raw : RawEntry R.args cells) :
    reindex (h ≫ k) raw = reindex h (reindex k raw) :=
  Proofs.reindex_comp h k raw

/-- At a decoded entry, the existing observer returns the native word and every cell. -/
theorem observe_eq_some_iff_native (graph : Graph P.args) {raw : RawEntry P.args cells}
    {entry : Entry P.args cells} (decoded : decode raw = some entry) (word : Word) (final : Heap cells) :
    observe graph raw = Part.some (encodeResult word final) ↔ nativeReturns graph entry.model entry.heap word final :=
  Proofs.observe_eq_some_iff_native graph decoded word final

theorem observe_eq_none_iff_native (graph : Graph P.args) {raw : RawEntry P.args cells}
    {entry : Entry P.args cells} (decoded : decode raw = some entry) :
    observe graph raw = Part.none ↔ (nativeReturns graph entry.model).NoReturn entry.heap :=
  Proofs.observe_eq_none_iff_native graph decoded

/-- Re-emitting at renamed typed ports agrees with pulling back an
admissible raw entry, including when no finite result exists. -/
theorem observe_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (raw : RawEntry Q.args cells)
    (entered : Admissible raw) :
    observe (mapGraph h graph) raw = observe graph (reindex h raw) :=
  Proofs.observe_mapGraph h graph raw entered

/-- Every initialized heap and typed valuation at a fixed cell count is
represented by one admissible raw entry. -/
theorem satisfaction (e : Equation P) (cells : Nat) :
    Holds e cells ↔ ∀ input : Tuple (Val cells) P.args, e.Holds (⟨cells, input⟩ : EntryModel P) :=
  Proofs.satisfaction e cells

/-- After renaming, quantify over the pullbacks of the target valuations. -/
theorem satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (cells : Nat) :
    Holds (e.map h) cells ↔ ∀ input : Tuple (Val cells) Q.args,
      e.Holds (reduct h (⟨cells, input⟩ : EntryModel Q)) :=
  (satisfaction (e.map h) cells).trans (forall_congr' fun input => e.satisfaction h ⟨cells, input⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry
