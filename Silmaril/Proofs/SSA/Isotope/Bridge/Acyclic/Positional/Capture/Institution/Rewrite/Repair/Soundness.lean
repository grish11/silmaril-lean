module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open CategoryTheory CategoryTheory.Limits
open Isotope.LetCase.LocallyNameless (AbortCongr Derivation Tm)
open Isotope.LetCase.Semantics.Categorical (denote)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty P.Instr n} {A : τ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

theorem empties_witnessed_proof (tail : List (Ty Empty)) : SequencesEmpty (EmptySequencing.equation tail) := by
  apply AbortCongr.let₁ (.sequence EmptySequencing.scrutinee) (.refl _)

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] {J : V ⥤ C}

section Freyd

variable [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]

theorem denote_sequencesEmpty_proof (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {d : Derivation P.Instr Γ₀ β a A} {e : Derivation P.Instr Γ₀ β b A}
    (h : AbortCongr Γ₀ d e) :
    letI := I
    denote J M d = denote J M e := by
  let _ := I
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | sequence d => exact (denote_emptySequencing M I d _).symm
  | op _ ih | inl _ ih | inr _ ih | abort _ ih => simp only [denote, ih]
  | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [denote, ih₁, ih₂]
  | case _ _ _ ih₁ ih₂ ih₃ => simp only [denote, ih₁, ih₂, ih₃]

theorem freydSat_sequencesEmpty_proof (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    (e : GrammarEquation P) (h : SequencesEmpty e) :
    ((LetCase.inst Γ₀).obj P).Sat (freydCaseAlgebra J M I) (grammarCase e) := by
  let _ := I
  apply (LetCase.sat_iff Γ₀ P _ (grammarCase e).2.1.2 (grammarCase e).2.2.2).mpr
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote]
  exact denote_sequencesEmpty_proof M I h

end Freyd

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

theorem sat_sequencesEmpty_proof (B : (grammarRoom J P).Mod) (e : GrammarEquation P)
    (h : SequencesEmpty e) : (grammarRoom J P).Sat B e := by
  let A := B.fromShrinkHoms.as
  change ((LetCase.inst Γ₀).obj P).Sat A.algebra (grammarCase e)
  rw [← A.presentation]
  exact freydSat_sequencesEmpty_proof A.expand.types A.expand.instructions e h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
