module

public import SqliteWasm.WholeModule

public section

namespace SqliteWasm

open Silmaril.Wasm

set_option maxRecDepth 220000
set_option maxHeartbeats 700000

theorem reactorDataLengths : sqlite.data.map (·.bytes.size) = [51370, 6924] := by decide +kernel

theorem reactorElementLengths : sqlite.elems.map (·.init.length) = [342] := by decide +kernel

theorem reactorSegmentBounds :
    sqlite.elems.length ≤ 2 ^ 32 ∧ sqlite.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ sqlite.data, d.bytes.size < 2 ^ 32) ∧
      (∀ e ∈ sqlite.elems, e.init.length < 2 ^ 32) := by
  have dataCount : sqlite.data.length = 2 := by
    have h := congrArg List.length reactorDataLengths
    rw [List.length_map] at h
    exact h
  have elementCount : sqlite.elems.length = 1 := by
    have h := congrArg List.length reactorElementLengths
    rw [List.length_map] at h
    exact h
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro d hd
    have size := List.mem_map_of_mem (f := fun d : Data => d.bytes.size) hd
    rw [reactorDataLengths] at size
    simp only [List.mem_cons, List.not_mem_nil, or_false] at size
    omega
  · intro e he
    have size := List.mem_map_of_mem (f := fun e : Elem => e.init.length) he
    rw [reactorElementLengths] at size
    simp only [List.mem_singleton] at size
    omega

end SqliteWasm
