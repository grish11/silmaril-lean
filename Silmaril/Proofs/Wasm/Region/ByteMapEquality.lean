module

public import Silmaril.Wasm.Region.ByteMap.Equality.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Equality.Proofs

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem equal_iff (a : Instr) : ∀ b, equal a b = true ↔ a = b := by
  induction a using Instr.rec
      (motive_2 := fun xs => ∀ ys, equalList xs ys = true ↔ xs = ys) <;>
    (first | (intro b; cases b) | (rename_i b; cases b)) <;>
    dsimp only [equal, equalList] <;> simp_all [and_assoc]
  all_goals
    constructor
    · rintro ⟨h, eq⟩; cases h
      exact ⟨rfl, heq_of_eq eq⟩
    · rintro ⟨h, heq⟩; cases h
      exact ⟨rfl, eq_of_heq heq⟩

end Silmaril.Wasm.Region.ByteMap.Equality.Proofs
