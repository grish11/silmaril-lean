module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Unit
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Validity

/-! # Categorical completeness at a packed structural input -/

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical

open CategoryTheory CategoryTheory.Limits
open LocallyNameless (Derivation Equiv)
open LetIter.Semantics.Categorical (boundEnv boundObj)
open scoped MonoidalCategory Structural

variable {α Φ : Type} [Signature α Φ]

/-- The chosen trace tensor is the shared product, with identity comparison. -/
theorem trace_shared_tensor (X Y : Type) :
    ∃ h : (traceJ (α := α) (Φ := Φ)).obj X ⊗ (traceJ (α := α) (Φ := Φ)).obj Y =
        (traceJ (α := α) (Φ := Φ)).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := traceJ (α := α) (Φ := Φ)) X Y = eqToIso h :=
  trace_shared_proof X Y

/-- Every lifted pure value map is central, including structural copy and discard. -/
theorem trace_pure_central {X Y : Type} (f : X ⟶ Y) :
    PremonoidalCategory.IsCentral ((traceJ (α := α) (Φ := Φ)).map f) :=
  FreydCategory.image_central _ f

/-- The categorical interpretation uses the original primitive trace model. -/
theorem traceArrow_apply {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (ρ : boundObj (traceTypes α) β) :
    (traceArrow d).of (PUnit.unit, ρ) = run d (boundEnv Value ρ) :=
  traceArrow_apply_proof d ρ

theorem traceArrow_apply_packed {s : Shape α} {t : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) (value : Value s.ty) :
    (traceArrow d).of (PUnit.unit, (PUnit.unit, value)) = run d (packedEnv s value) :=
  traceArrow_apply_packed_proof d value

/-- Native soundness holds for arbitrary typed contexts in the chosen class. -/
theorem valid_of_equiv {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A)
    (h : Equiv false Γ₀ β t u A) : Valid d e :=
  valid_of_equiv_proof d e h

theorem traceArrow_of_valid {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    {d : Derivation Φ Γ₀ β t A} {e : Derivation Φ Γ₀ β u A} (h : Valid d e) :
    traceArrow d = traceArrow e :=
  traceArrow_of_valid_proof h

/-- Equality in the single ordered-trace Kleisli model reflects the native
equation at any packed structural input. -/
theorem traceArrow_eq_iff_native {s : Shape α} {t u : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) (e : Derivation Φ Γ₀ (Packed s) u A) :
    traceArrow d = traceArrow e ↔ Equiv false Γ₀ (Packed s) t u A :=
  ⟨equiv_of_traceArrow_proof, fun h => traceArrow_of_valid (valid_of_equiv d e h)⟩

/-- Native derivability is exactly equality in every coherent central-unit
model with shared tensors in the selected locally small Freyd class. -/
theorem equiv_iff_valid {s : Shape α} {t u : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) (e : Derivation Φ Γ₀ (Packed s) u A) :
    Equiv false Γ₀ (Packed s) t u A ↔ Valid d e :=
  ⟨valid_of_equiv d e, fun h => (traceArrow_eq_iff_native d e).mp (traceArrow_of_valid h)⟩

/-- Cartesian terminality belongs to the value category. With an available
event, the tensor unit on the computation side has distinct endomorphisms. -/
theorem traceUnit_not_terminal (event : Event (α := α) (Φ := Φ)) :
    ¬ Nonempty (IsTerminal (𝟙_ (Kleisli (ofTypeMonad (Trace α Φ))))) :=
  traceUnit_not_terminal_proof event

end Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical
