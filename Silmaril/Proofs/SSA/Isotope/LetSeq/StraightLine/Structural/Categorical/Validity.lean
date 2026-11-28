module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Defs
import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical

open CategoryTheory
open LocallyNameless (Derivation Equiv)
open LetIter.Semantics.Categorical
open scoped MonoidalCategory Structural

variable {α Φ : Type} [Signature α Φ]

set_option backward.isDefEq.respectTransparency false

theorem traceArrow_apply_proof {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (ρ : boundObj (traceTypes α) β) :
    (traceArrow d).of (PUnit.unit, ρ) = run d (boundEnv Value ρ) := by
  simp only [traceArrow, denoteOfType_eq, asIter, Morphism.CaseIter.denote_derivation,
    Morphism.SeqCase.denote_derivation, run]
  congr 1
  funext x
  exact x.elim

theorem trace_shared_proof (X Y : Type) :
    ∃ h : (traceJ (α := α) (Φ := Φ)).obj X ⊗ (traceJ (α := α) (Φ := Φ)).obj Y =
        (traceJ (α := α) (Φ := Φ)).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := traceJ (α := α) (Φ := Φ)) X Y = eqToIso h :=
  ⟨rfl, rfl⟩

theorem traceArrow_of_valid_proof {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    {d : Derivation Φ Γ₀ β t A} {e : Derivation Φ Γ₀ β u A} (h : Valid d e) :
    traceArrow d = traceArrow e := by
  classical
  let := traceInstructions (α := α) (Φ := Φ)
  exact h (traceJ (α := α) (Φ := Φ)) (traceTypes α)
    (typingCoherent_ofType (ν := Empty) (fun _ : α => Nat) (model (Φ := Φ)))
    trace_shared_proof (fun _ hf => by cases hf)

theorem valid_of_equiv_proof {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) (h : Equiv false Γ₀ β t u A) :
    Valid d e := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr coherent shared pureInstr
  exact denote_equiv_of_coherent_shared_tensor J M coherent shared pureInstr
    (Morphism.CaseIter.embed_equiv (Morphism.SeqCase.embed_equiv h)) (asIter d) (asIter e)

theorem traceArrow_apply_packed_proof {s : Shape α} {t : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) (value : Value s.ty) :
    (traceArrow d).of (PUnit.unit, (PUnit.unit, value)) = run d (packedEnv s value) := by
  rw [traceArrow_apply_proof]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => k.elim0) i

theorem equiv_of_traceArrow_proof {s : Shape α} {t u : Term Φ 1} {A : Ty α}
    {d : Derivation Φ Γ₀ (Packed s) t A} {e : Derivation Φ Γ₀ (Packed s) u A}
    (h : traceArrow d = traceArrow e) : Equiv false Γ₀ (Packed s) t u A := by
  let value := s.fresh 0
  have eval := congrArg (fun f => f.of (PUnit.unit, (PUnit.unit, value))) h
  rw [traceArrow_apply_packed_proof, traceArrow_apply_packed_proof] at eval
  exact (packed_run_eq_iff_native d e).mp eval

end Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical
