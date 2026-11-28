module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Laws.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open CategoryTheory CategoryTheory.Limits
open Isotope.LetCase.LocallyNameless (Derivation Tm)
open Isotope.LetCase.Semantics.Categorical (denote)
open LambdaSSA.Acyclic (Operand)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

set_option backward.isDefEq.respectTransparency false

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] {J : V ⥤ C}
  {n : Nat} {β : BoundCtx τ n}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

section Freyd

variable [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]

/-- Postcompose the checked let-η law with the interpreted empty elimination. -/
theorem denote_abortSequence_proof (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {t : Tm Empty P.Instr n} (a : Derivation P.Instr Γ₀ β t (empty : τ)) (A : τ) :
    letI := I
    denote J M (.let₁ a (.abort (C := A) (.bv (ι := 0)))) = denote J M (.abort (C := A) a) := by
  let _ := I
  have eta := (LetCase.sat_iff Γ₀ P (freydCaseAlgebra J M I) (.let₁ a (.bv (ι := 0))) a).mp
    (freydCaseAlgebra_sat_letReturn M I a)
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote] at eta
  let p := J.map (M.emptyIsInitial.to (M.obj A))
  calc
    _ = denote J M (.let₁ a (.bv (ι := 0))) ≫ p := by simp only [denote, LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc, p]
    _ = _ := congrArg (fun f => f ≫ p) eta

omit [FreydCategory.CentralUnit J] in
private theorem returnUnit_denote_congr (M : TypeModel τ V) [InstructionModel J M P.Instr]
    (L : List τ) {a b : Operand P.Instr β (unit : τ)}
    (eq : denote J M a.2 = denote J M b.2) :
    denote J M (returnUnit L a).toLetCase.2 = denote J M (returnUnit L b).toLetCase.2 := by
  change bindArrow J (denote J M a.2) _ = bindArrow J (denote J M b.2) _
  rw [eq]
  rfl

end Freyd

namespace EmptySequencing

theorem freyd_sat_proof [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel (Ty Empty) V) (I : InstructionModel J M signature.Instr)
    (tail : List (Ty Empty)) :
    ((LetCase.inst (Ctx.nil : Ctx Empty (Ty Empty))).obj signature).Sat
      (freydCaseAlgebra J M I) (grammarCase (equation tail)) := by
  let _ := I
  apply (LetCase.sat_iff _ signature (freydCaseAlgebra J M I)
    (returnUnit tail direct).toLetCase.2 (returnUnit tail sequenced).toLetCase.2).mpr
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote]
  exact returnUnit_denote_congr M tail
    (denote_abortSequence_proof M I scrutinee Ty.unit).symm

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

theorem sat_proof (tail : List (Ty Empty)) (A : (grammarRoom J signature).Mod) :
    (grammarRoom J signature).Sat A (equation tail) := by
  let B := A.fromShrinkHoms.as
  change ((LetCase.inst (Ctx.nil : Ctx Empty (Ty Empty))).obj signature).Sat B.algebra
    (grammarCase (equation tail))
  rw [← B.presentation]
  exact freyd_sat_proof B.expand.types B.expand.instructions tail

end EmptySequencing
end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
