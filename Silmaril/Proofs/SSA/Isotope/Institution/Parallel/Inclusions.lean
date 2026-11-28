module

public import Silmaril.SSA.Isotope.Institution.Parallel.Inclusions.Defs

@[expose] public section

namespace Silmaril.Isotope.Parallel.InstitutionProofs

open Silmaril.Isotope.Institution Parallel.Institution CategoryTheory Semantics

universe u v q

section Control

variable {τ : Type u} (D : τ → Type q) (m : Type q → Type q)

theorem lowerControl_seq (h : Tier.seq ≠ .iter) :
    lowerControl h (Control.seq D Id) m = Control.seq D m := by
  have eqLoop : (@(lowerControl h (Control.seq D Id) m).loop) =
      @(Control.seq D m).loop := by
    funext hi
    exact (h hi).elim
  exact congrArg (fun loop => { (Control.seq D m) with loop }) eqLoop

theorem lowerControl_case [CoproductTypeFormers τ] [CoproductModel D] [EmptyModel D]
    (h : Tier.case ≠ .iter) :
    lowerControl h (Control.case D Id) m = Control.case D m := by
  have eqLoop : (@(lowerControl h (Control.case D Id) m).loop) =
      @(Control.case D m).loop := by
    funext hi
    exact (h hi).elim
  exact congrArg (fun loop => { (Control.case D m) with loop }) eqLoop

end Control

variable {τ ε : Type u} {S S' : InstrSig τ ε} {ν : Type v} [DecidableEq ν] [TypeFormers τ]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : LetPar.Tm ν S.Instr n} {A : τ}

private theorem widen_cast {B : τ} (h : A = B) (d : Derivation S.Instr Γ β t A) :
    LetParCase.ofLetParDerivation (Derivation.castResult h d) =
      Derivation.castResult h (LetParCase.ofLetParDerivation d) := by
  cases h
  rfl

theorem widen_derivation_map (f : S ⟶ S') (d : Derivation S.Instr Γ β t A) :
    HEq ((LetParCase.ofLetParDerivation d).mapInstr f)
      (LetParCase.ofLetParDerivation (d.mapInstr f)) := by
  induction d with
  | @op k b a p d ih =>
      change HEq (Derivation.castResult (f.target p)
        (Derivation.op (f := f.instr p) (Derivation.castResult (f.source p).symm
          ((LetParCase.ofLetParDerivation d).mapInstr f))))
        (LetParCase.ofLetParDerivation (Derivation.castResult (f.target p)
          (Derivation.op (f := f.instr p) (Derivation.castResult (f.source p).symm
            (d.mapInstr f)))))
      rw [widen_cast]
      change HEq _ (Derivation.castResult (f.target p)
        (Derivation.op (f := f.instr p)
          (LetParCase.ofLetParDerivation (Derivation.castResult (f.source p).symm (d.mapInstr f)))))
      rw [widen_cast]
      simp only [Derivation.castResult, eqRec_heq_iff, heq_eqRec_iff]
      congr 1
      · exact Tm.mapInstr_widen Tier.seqCase f.instr a
      · simpa only [eqRec_heq_iff, heq_eqRec_iff] using ih
  | inl | inr | case | abort => exact (‹Tier.HasCase .seq› rfl).elim
  | iter => exact nomatch ‹Tier.HasIter .seq›
  | _ =>
      simp only [LetParCase.ofLetParDerivation, Derivation.mapInstr, LetParCase.ofLetPar,
        Parallel.Tm.widen, Parallel.Tm.mapInstr]
      congr 1 <;> exact Tm.mapInstr_widen Tier.seqCase f.instr _

theorem equation_widen_map (f : S ⟶ S') (φ : Equation S .seq Γ) :
    φ.ofLetPar.map f = (φ.map f).ofLetPar := by
  cases φ
  unfold Equation.map Equation.ofLetPar
  congr 1
  all_goals first | exact Tm.mapInstr_widen Tier.seqCase f.instr _ | exact widen_derivation_map f _

end Silmaril.Isotope.Parallel.InstitutionProofs
