module

public import Silmaril.Formats.JsonBytes.Decide.Thms
public import Silmaril.Formats.JsonBytes.Thms
public import Mathlib.Data.Set.Finite.Basic

/-!
# The JSON byte language is infinite: proof

For every `n`, `n` spaces followed by the number `0` is a JSON text (`ws value ws`, RFC 8259
§2): the spaces are whitespace and `0` is a scalar value (checked by Mathlib's regular
expression matcher). These texts have distinct lengths.

New proof.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.WIT

open Silmaril.Formats.JsonBytes

/-- `n` spaces, then `0`. -/
def spacedZero (n : Nat) : List UInt8 := List.replicate n 0x20 ++ [0x30]

theorem zero_mem_scalar (p : Profile) : [0x30] ∈ (scalar p).matches' := by
  rw [← RegularExpression.rmatch_iff_matches']
  cases p <;> decide

theorem spacedZero_mem (p : Profile) (n : Nat) : spacedZero n ∈ language p := by
  refine ⟨List.replicate n 0x20, [0x30], [], ?_, .scalar (zero_mem_scalar p), ?_, by simp [spacedZero]⟩
  · rw [mem_ws]
    intro b hb
    rw [List.eq_of_mem_replicate hb]
    exact Or.inl rfl
  · rw [mem_ws]; simp

theorem language_infinite (p : Profile) : (language p : Set (List UInt8)).Infinite :=
  Set.infinite_of_injective_forall_mem (f := spacedZero)
    (fun a b h => by simpa [spacedZero] using congrArg List.length h)
    (spacedZero_mem p)

end Silmaril.Proofs.Wasm.Component.Reference.WIT
