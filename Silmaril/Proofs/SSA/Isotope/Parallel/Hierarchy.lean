module

public import Silmaril.SSA.Isotope.LetParCase.Thms
public import Silmaril.SSA.Isotope.LetParIter.Thms
public import Silmaril.SSA.Isotope.Parallel.Hierarchy.Defs
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic

public section

namespace Silmaril.Isotope.Parallel.Hierarchy.Proofs

universe u v w q

variable {τ : Type u} [TypeFormers τ] {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

private def pack {tier : Tier} [CaseTypes tier τ] {t : Tm tier ν Φ n}
    (d : Derivation Φ Γ β t A) : (a : Tm tier ν Φ n) × Derivation Φ Γ β a A := ⟨t, d⟩

theorem seqCase_derivation {t : LetSeq.LocallyNameless.Tm ν Φ n}
    (d : LetSeq.LocallyNameless.Derivation Φ Γ β t A) :
    (⟨_, LetParCase.derivation (Morphism.SeqCase.derivation d)⟩ :
      (a : LetParCase.Tm ν Φ n) × Derivation Φ Γ β a A) =
        ⟨_, LetParCase.ofLetParDerivation (LetPar.derivation d)⟩ := by
  induction d with
  | fv | bv | unit => rfl
  | @op _ _ f _ _ ih => exact congrArg (fun a => pack (Derivation.op (f := f) a.2)) ih
  | let₁ _ _ iha ihb => exact congrArg₂ (fun a b => pack (Derivation.let₁ a.2 b.2)) iha ihb
  | pair _ _ iha ihb => exact congrArg₂ (fun a b => pack (Derivation.pair a.2 b.2)) iha ihb
  | let₂ _ _ iha ihb => exact congrArg₂ (fun a b => pack (Derivation.let₂ a.2 b.2)) iha ihb

theorem caseIter_derivation {t : LetCase.LocallyNameless.Tm ν Φ n}
    (d : LetCase.LocallyNameless.Derivation Φ Γ β t A) :
    (⟨_, LetParIter.derivation (Morphism.CaseIter.derivation d)⟩ :
      (a : LetParIter.Tm ν Φ n) × Derivation Φ Γ β a A) =
        ⟨_, LetParIter.ofLetParCaseDerivation (LetParCase.derivation d)⟩ := by
  induction d with
  | fv | bv | unit => rfl
  | @op _ _ f _ _ ih => exact congrArg (fun a => pack (Derivation.op (f := f) a.2)) ih
  | let₁ _ _ iha ihb => exact congrArg₂ (fun a b => pack (Derivation.let₁ a.2 b.2)) iha ihb
  | pair _ _ iha ihb => exact congrArg₂ (fun a b => pack (Derivation.pair a.2 b.2)) iha ihb
  | let₂ _ _ iha ihb => exact congrArg₂ (fun a b => pack (Derivation.let₂ a.2 b.2)) iha ihb
  | @inl _ _ _ _ B _ ih => exact congrArg (fun a => pack (Derivation.inl (h := LetParIter.hasCase) (B := B) a.2)) ih
  | @inr _ _ _ A _ _ ih => exact congrArg (fun a => pack (Derivation.inr (h := LetParIter.hasCase) (A := A) a.2)) ih
  | case _ _ _ ihe ihl ihr =>
    exact congr (congrArg₂ (fun e l r => pack (Derivation.case (h := LetParIter.hasCase) e.2 l.2 r.2)) ihe ihl) ihr
  | @abort _ _ _ C _ ih => exact congrArg (fun a => pack (Derivation.abort (h := LetParIter.hasCase) (C := C) a.2)) ih

open Isotope.Semantics

variable {D : τ → Type q} {m : Type q → Type q}

theorem denote_ofLetParCase [ProductModel D] [UnitModel D] [Monad m]
    (M : InstructionModel D Φ m) (P : ParOp m) (C : Control .iter D m)
    {t : LetParCase.Tm ν Φ n} (d : Derivation Φ Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (LetParIter.ofLetParCaseDerivation d).denote D M P C γ ρ =
      d.denote D M P (restrictControl C) γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | iter => exact nomatch ‹Tier.HasIter .case›
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [LetParIter.ofLetParCaseDerivation, LetParIter.ofLetParCase, Tm.widen,
      Derivation.denote, restrictControl]
    congr 1
    exact ih ρ
  | let₁ _ _ iha ihb | let₂ _ _ iha ihb =>
    simp only [LetParIter.ofLetParCaseDerivation, LetParIter.ofLetParCase, Tm.widen, Derivation.denote]
    congr 1
    · exact iha ρ
    · exact funext fun _ => ihb _
  | pair _ _ iha ihb =>
    simp only [LetParIter.ofLetParCaseDerivation, LetParIter.ofLetParCase, Tm.widen, Derivation.denote]
    congr 1
    · exact iha ρ
    · funext a
      congr 1
      exact ihb ρ
  | par _ _ iha ihb =>
    simp only [LetParIter.ofLetParCaseDerivation, LetParIter.ofLetParCase, Tm.widen, Derivation.denote]
    congr 1
    congr 1
    · exact iha ρ
    · exact ihb ρ
  | case _ _ _ ihe ihl ihr =>
    simp only [LetParIter.ofLetParCaseDerivation, LetParIter.ofLetParCase, Tm.widen,
      Derivation.denote, restrictControl]
    congr 1
    · exact ihe ρ
    · funext s
      cases C.sum _ _ _ s with
      | inl a => exact ihl (ρ.snoc a)
      | inr b => exact ihr (ρ.snoc b)

end Silmaril.Isotope.Parallel.Hierarchy.Proofs
