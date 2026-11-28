module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Model.Defs

/-! # Interpret the handoff as guarded data routing with unchanged state -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (pack packChoice point)
open TwoBlock.TwoExit (enter ExitCode callCase)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A M E D : τ}

def model : OrderedRuntime.Structured.Model (TwoBlock.TwoExit.Pure τ) (Effect Φ) (StateT σ Part.{u}) where
  value := TyDen
  runPure := (ExplicitRuntime.orderedModel (Φ := Φ) (ε := ε) (σ := σ)).runPure
  effect
    | .loop e, input => (ExplicitRuntime.orderedModel (Φ := Φ) (ε := ε) (σ := σ)).effect e input
    | .nested e, input => (NestedFeedback.orderedModel (Φ := Φ) (ε := ε) (σ := σ)).effect e input
    | @Effect.enterNested _ _ _ _ A M, .cons value .nil =>
      match TypeModel.coprodEquiv (ExitCode M M) A value with
      | .inl _ => StateT.mk fun _ => Part.none
      | .inr a => pure (pack (NestedFeedback.start (D := M) a))
    | @Effect.exitNested _ _ _ _ A M, .cons value .nil =>
      match TypeModel.coprodEquiv M A value with
      | .inl result => pure (pack (TwoBlock.TwoExit.finish (A := A) (C := M) (D := M) (.inl result)))
      | .inr _ => StateT.mk fun _ => Part.none
    | .classifyPayload op, .cons value .nil => callCase (ε := ε) op value >>= fun result =>
      pure (packChoice result)
    | .enterCarrier, .cons value .nil => pure (pack (enter value))
    | @Effect.link _ _ _ _ A M E D, .cons payload .nil =>
      match TypeModel.coprodEquiv (ExitCode M M) A payload with
      | .inl e => pure (pack (enter (A := M) (C := E) (D := D)
          (Sum.elim id id (TypeModel.coprodEquiv M M e))))
      | .inr _ => StateT.mk fun _ => Part.none
    | @Effect.routeExit _ _ _ _ H E M D, .cons payload .nil =>
      match TypeModel.coprodEquiv (ExitCode E M) H payload with
      | .inl exit =>
        match TypeModel.coprodEquiv E M exit with
        | .inl e => pure (ExplicitRuntime.choiceData (.inl
            ((TypeModel.coprodEquiv E D).symm (.inl e))))
        | .inr input => pure (ExplicitRuntime.choiceData (.inr input))
      | .inr _ => StateT.mk fun _ => Part.none

abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel (model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))

noncomputable def observe (g : Graph Φ A M E D) (input : TyDen A) (token : σ) :=
  NestedTheta.Partial.observe (wireModel (ε := ε)) g (point (enter input) token)

def returns (g : Graph Φ A M E D) (input : TyDen A) (initial : σ) (label : LabelDen [E,D]) (final : σ) :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) g (point (enter input) initial)
    (ExplicitRuntime.exitTuple (A := M) (label, final))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires
