module

public import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Empty.Sequencing
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Empty.Reflection

/-! # Empty elimination and reflection in exact LetIter -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Categorical empty elimination can sequence its scrutinee explicitly. -/
theorem denote_let_abort {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    (d : Derivation Φ Γ β t (empty : τ)) (A : τ) :
    denote J M (.let₁ d (.abort (C := A) (.bv (ι := 0)))) = denote J M (.abort (C := A) d) :=
  denote_let_abort_proof J M d A

end Silmaril.Isotope.LetIter.Semantics.Categorical


namespace Silmaril.Isotope.LetIter.LocallyNameless

universe u v w r

/-- The exact theory can sequence an empty scrutinee when the scrutinee is pure. -/
theorem equiv_let_abort_of_pure {τ : Type u} [TypeFormers τ]
    {Φ : Type v} [HasTy Φ τ] {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
    {pe : ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β a (empty : τ)) (hp : Pure pe a) :
    Equiv pe Γ β (.let₁ a (.abort (.bv 0))) (.abort a) A :=
  .ax (.structural (.letBeta hp)) (.let₁ h (.abort .bv)) (.abort h)

end Silmaril.Isotope.LetIter.LocallyNameless

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample

/-- Explicit sequencing of an effectful empty scrutinee is independent of
the exact native rules in the existing counterexample signature. -/
theorem exact_abortSequence_unprovable :
    ¬ LocallyNameless.Equiv (Φ := signature.Instr) false (Ctx.nil : Ctx Empty (Ty Empty)) .nil
      (.abort (.op true .unit)) (.let₁ (.op true .unit) (.abort (.bv 0))) Ty.unit :=
  native_unprovable

end Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

/-- The existing exact quotient distinguishes closed terms with equal denotation in the
syntactic strong Elgot Freyd model. The witness sequences an effectful empty scrutinee. -/
theorem closedReflection_fails : ¬ ClosedReflection :=
  AbortCounterexample.closedReflection_fails_proof

/-- Native denotation fails to reify into every packed syntax class, already for closed terms. -/
theorem closedReification_fails : ¬ ClosedReification :=
  AbortCounterexample.closedReification_fails_proof

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
