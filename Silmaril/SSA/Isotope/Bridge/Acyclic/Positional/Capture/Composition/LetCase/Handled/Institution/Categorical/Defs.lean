module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Defs

/-! # Categorical validity at chosen universes and two free models

The existing validity class quantifies over coherent, shared-tensor,
central-unit strong Elgot Freyd models whose objects are in `Type 1` and
whose homs are in `Type`. The ordered trace monad is an endofunctor on
`Type`, so its Kleisli category is a model in that class. The tree monad
over the free requests sends `Type 1` to `Type 1`, so its Kleisli category
has objects in `Type 2` and homs in `Type 1`. It satisfies the same
conditions one universe up and is outside the existing class only for that
reason.

`ValidAt` states the same validity at chosen universes. At the universes
of the existing class it is the existing validity by definition.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel)
open LetIter.Semantics.Categorical (TypeModel InstructionModel TypingCoherent denote ofTypeModel ofInstructionModel
  denoteOfType)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open Silmaril.Elgot.ITree (Tree)
open Free (Events Val model)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe u₁ u₂ v₁ v₂

section Validity

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {n : Nat} {β : BoundCtx τ n} {a b : LetIter.LocallyNameless.Tm Empty Φ n} {A : τ}

/-- Equality in all coherent shared-tensor, central-unit strong Elgot Freyd
models with pure primitive interpretations, with objects and homs in the
chosen universes. The free context is empty. -/
def ValidAt (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) : Prop :=
  ∀ {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) [InstructionModel J M Φ],
    TypingCoherent (ν := Empty) J M Φ →
    (∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e) →
    (∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p) →
    denote J M da = denote J M db

end Validity

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-- Validity of a pair of LetCase operands at chosen universes, through
the existing inclusion of LetCase derivations. -/
def CaseValidAt {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B) : Prop :=
  ValidAt.{u₁, u₂, v₁, v₂} false (Morphism.CaseIter.derivation a.2) (Morphism.CaseIter.derivation b.2)

/-- The ordered trace interpretation as a coherent region model of the
existing rooms. -/
noncomputable def traceRegionModel (Φ : Type) [LetCase.Structural.Finite.Signature Φ] :
    CoherentRegionModel (traceJ (α := Empty) (Φ := Φ)) (sig Φ) :=
  ⟨traceTypes Empty, traceInstructions, Native.trace_region_coherent⟩

/-- The Kleisli arrow of a LetCase derivation at the free tree
interpretation. Its Kleisli category has objects in `Type 2`. -/
noncomputable def treeArrow {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty Empty}
    (d : LetCase.LocallyNameless.Derivation Φ Γ₀ γ t A) :=
  denoteOfType Val (model Φ) (Morphism.CaseIter.derivation d)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
