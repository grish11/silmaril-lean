module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Native
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Models

/-! # A missing native equation on the witnessed LetCase grammar -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open CategoryTheory CategoryTheory.Limits
open Isotope.LetCase.LocallyNameless (Equiv)
open Isotope.LetCase.LocallyNameless.Models (syntacticModel)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ ε Φ : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {P : InstrSig τ ε} {n : Nat} {β : BoundCtx τ n} {pe : ε}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- A pure case decoder cancels the captured entry binder and the first exit
tag in the native rewrite relation using case β, pure-let β, and let η. -/
theorem returnUnit_reflects (L : List τ) (a b : Operand Φ β (unit : τ))
    (h : Equiv pe Γ₀ β (returnUnit L a).toLetCase.1 (returnUnit L b).toLetCase.1
      (packedExitType ((unit : τ) :: L))) : Equiv pe Γ₀ β a.1 b.1 (unit : τ) :=
  reflect_returnUnit L a b h

/-- The existing native term model tests derivability of the witnessed
equation, using the exact typed LetCase congruence. -/
theorem syntactic_sat_iff (pe : ε) (e : GrammarEquation P) :
    ((LetCase.inst Γ₀).obj P).Sat (syntacticModel (Φ := P.Instr) pe Γ₀).algebra
      (grammarCase e) ↔ Derivable pe e :=
  syntactic_sat_iff_proof pe e

section EmptyDenotation

open Isotope.LetCase.LocallyNameless (Derivation Tm)
open Isotope.LetCase.Semantics.Categorical (denote)

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] {J : V ⥤ C}
  [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]

/-- Sequence an empty result once before eliminating it, even when its
producer has effects. -/
theorem denote_emptySequencing (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {t : Tm Empty P.Instr n} (a : Derivation P.Instr Γ₀ β t (empty : τ)) (A : τ) :
    letI := I
    denote J M (.let₁ a (.abort (C := A) (.bv (ι := 0)))) = denote J M (.abort (C := A) a) :=
  denote_abortSequence_proof M I a A

end EmptyDenotation

namespace EmptySequencing

local notation "T" => Ty Empty
local notation "Γ" => (Ctx.nil : Ctx Empty T)

/-- The witnessed equation is independent of the native rules at the pure
effect `false`, even with arbitrary unused tail exits. -/
theorem unprovable (tail : List T) : ¬ Derivable false (equation tail) :=
  unprovable_proof tail

theorem syntactic_rejects (tail : List T) :
    ¬ ((LetCase.inst Γ).obj signature).Sat
      (syntacticModel (Φ := signature.Instr) false Γ).algebra (grammarCase (equation tail)) :=
  fun h => unprovable tail ((syntactic_sat_iff false (equation tail)).mp h)

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] {J : V ⥤ C}

/-- The model equation is already forced by a distributive Freyd
interpretation with central unit. Iteration plays no role in it. -/
theorem freyd_sat [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel T V) (I : InstructionModel J M signature.Instr) (tail : List T) :
    ((LetCase.inst Γ).obj signature).Sat (freydCaseAlgebra J M I) (grammarCase (equation tail)) :=
  freyd_sat_proof M I tail

/-- The native operation-algebra term model cannot have a presentation of
the kind required by the validated room. -/
theorem syntacticModel_noFreyd [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel T V) (I : InstructionModel J M signature.Instr) :
    freydCaseAlgebra J M I ≠ (syntacticModel (Φ := signature.Instr) false Γ).algebra :=
  fun presentation => syntactic_rejects [] (presentation ▸ freyd_sat M I [])

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

/-- Every model of the existing witnessed grammar room satisfies this
equation at the original ordered exit interface. -/
theorem sat (tail : List T) (A : (grammarRoom J signature).Mod) :
    (grammarRoom J signature).Sat A (equation tail) :=
  sat_proof tail A

/-- Native rewrite derivability fails to reflect validity in the entire
validated room, already with two outward positions of identical type. -/
theorem incomplete :
    ¬ ∀ e : GrammarEquation signature,
      (∀ A : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat A e) → Derivable false e :=
  fun reflect => unprovable [.unit] (reflect (equation [.unit]) (sat [.unit]))

/-- A single validated model cannot reflect all witnessed equations either. -/
theorem no_separating_model :
    ¬ ∃ A : (grammarRoom J signature).Mod,
      ∀ e : GrammarEquation signature, (grammarRoom J signature).Sat A e → Derivable false e := by
  rintro ⟨A, reflect⟩
  exact unprovable [.unit] (reflect (equation [.unit]) (sat [.unit] A))

end EmptySequencing
end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
