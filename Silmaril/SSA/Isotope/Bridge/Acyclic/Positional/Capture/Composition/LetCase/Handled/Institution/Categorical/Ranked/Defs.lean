module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Thms

/-! # Validity of ranked sentences in the existing categorical ranked room

A model of the existing ranked room is a coherent region model over a
strong Elgot Freyd functor with central unit, with objects in `Type 1` and
homs in `Type`. Native soundness of LetCase equations needs three further
conditions on such a model, collected in `Supported`. They are the
conditions of the existing validity class of expressions.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation CoherentRegionModel)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation)
open Region (packedExitType)
open LetIter.Semantics.Categorical (InstructionModel TypingCoherent)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀ traceArrow)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section General

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}

/-- The LetCase operand emitted from a ranked entry by the checked emitter. -/
def emitted {d : Nat} {β : BoundCtx τ d} {L : List τ} (l : RankedEntry P.Instr β L) :
    Operand P.Instr β (packedExitType L) :=
  l.table.toLetCase l.checked l.index l.entry

/-- The two sides of a typed LetCase equation are natively equal. -/
def Derivable (pe : ε) (c : CaseEquation P) : Prop :=
  Equiv pe (Ctx.nil : Ctx Empty τ) c.1.bound c.2.1.1 c.2.2.1 c.1.result

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The conditions under which native LetCase equations are sound in a
model of the ranked room: coherent expression typing, a tensor shared
with the value category, and pure interpretations of pure primitives. -/
structure Supported (pe : ε) (K : CoherentRegionModel J P) : Prop where
  typing : letI := K.instructions; TypingCoherent (ν := Empty) J K.types P.Instr
  shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S),
    Functor.StrongPremonoidal.tensorIso (J := J) R S = eqToIso e
  pure : letI := K.instructions
    ∀ f : P.Instr, IsPure pe f → ∃ p : K.types.obj (instrSrc f) ⟶ K.types.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := K.types) f = J.map p

end General

/-- A ranked sentence holds in every supported model of the existing
ranked room, over every functor of the class. -/
def RankedValid {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε} (pe : ε) (e : RankedEquation P) : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (K : CoherentRegionModel J P), Supported pe K →
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
      (ShrinkHoms.toShrinkHoms (Discrete.mk K)) e

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-- Equal ordered trace arrows over this bound context give native
equality. This is the reflection property used for completeness. -/
def Separated {n : Nat} (γ : Context n) : Prop :=
  ∀ {t u : LetCase.LocallyNameless.Tm Empty Φ n} {D : Ty Empty} (d : Derivation Φ Γ₀ γ t D)
    (e : Derivation Φ Γ₀ γ u D), traceArrow d = traceArrow e → Equiv false Γ₀ γ t u D

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
