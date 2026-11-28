module

public import Silmaril.Formats.Arrow.BinaryView.Defs
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView

open Silmaril.Formats.Arrow.BinaryView

theorem readBinary_iff (buffers : Buffers) (index maxValueBytes : Nat) (value : KBytes) :
    readBinary buffers index maxValueBytes = .ok value ↔ Wire buffers index maxValueBytes value := by
  unfold readBinary Wire
  dsimp only
  generalize buffers.views.read (16 * index) 4 = length
  generalize buffers.views.read (16 * index + 8) 4 = bufferIndex
  generalize buffers.views.read (16 * index + 12) 4 = offset
  by_cases wf : buffers.views.wf = true
  · by_cases slot : 16 * index + 16 ≤ buffers.views.len
    · by_cases signed : length < 2^31
      · by_cases budget : length ≤ maxValueBytes
        · by_cases short : length ≤ 12
          · by_cases padding : buffers.views.read (16 * index + 4 + length) (12 - length) = 0
            all_goals simp [wf, slot, signed, budget, short, padding, Nat.not_lt_of_ge short]
          · by_cases reference : bufferIndex < 2^31 ∧ offset < 2^31
            · cases selected : buffers.data[bufferIndex]? with
              | none => simp [wf, slot, signed, budget, short, reference]
              | some data =>
                by_cases dataWf : data.wf = true
                · by_cases within : offset + length ≤ data.len
                  · by_cases matching : buffers.views.read (16 * index + 4) 4 = data.read offset 4
                    all_goals simp [wf, slot, signed, budget, short, reference, dataWf,
                      within, matching, Nat.lt_of_not_ge short]
                  · simp [wf, slot, signed, budget, short, reference, dataWf, within]
                · simp [wf, slot, signed, budget, short, reference, dataWf]
            · simp [wf, slot, signed, budget, short, reference]
        · simp [wf, slot, signed, budget]
      · simp [wf, slot, signed]
    · simp [wf, slot]
  · simp [wf]

theorem readUtf8_iff (buffers : Buffers) (index maxValueBytes : Nat) (text : String) :
    readUtf8 buffers index maxValueBytes = .ok text ↔
      ∃ bytes, Wire buffers index maxValueBytes bytes ∧
        String.fromUTF8? bytes.toByteArray = some text := by
  cases binary : readBinary buffers index maxValueBytes with
  | error error => simp [readUtf8, binary, ← readBinary_iff, bind, Except.bind]
  | ok bytes =>
    simp only [readUtf8, binary, ← readBinary_iff, Except.ok.injEq, exists_eq_left',
      bind, Except.bind]
    cases String.fromUTF8? bytes.toByteArray <;> simp [pure, Except.pure]

theorem readBinary_extent {buffers : Buffers} {index maxValueBytes : Nat} {value : KBytes}
    (read : readBinary buffers index maxValueBytes = .ok value) :
    value.wf = true ∧ value.len = buffers.views.read (16 * index) 4 ∧ value.len ≤ maxValueBytes := by
  obtain ⟨viewsWf, slot, _, budget, inline | external⟩ := (readBinary_iff _ _ _ _).1 read
  · obtain ⟨short, _, rfl⟩ := inline
    exact ⟨KBytes.wf_slice _ _ _ viewsWf (by omega), KBytes.len_slice _ _ _,
      KBytes.len_slice _ _ _ ▸ budget⟩
  · obtain ⟨_, _, data, _, dataWf, within, _, rfl⟩ := external
    exact ⟨KBytes.wf_slice _ _ _ dataWf within, KBytes.len_slice _ _ _,
      KBytes.len_slice _ _ _ ▸ budget⟩

end Silmaril.Proofs.Formats.Arrow.BinaryView
