module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Sequential
open OrderedTheta (point)
open TwoBlock.TwoExit (enter)
open NestedTheta
open NestedTheta.ExplicitRuntime (EntryChecked ThreadedOp boundaryResult)
open NestedTheta.ExplicitRuntime.Partial (abnormal abnormal_iff erasedModel returns_iff)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Flat.Serial.Graph Φ A X Z L E D sigs}

theorem run_eq_none_of_blocked (actions : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (checked : EntryChecked (a := Flat.Serial.payloadData A X Z) (b := Flat.Serial.payloadData L E D) g.toTerm)
    {input : TyDen A} {initial : σ}
    {attempt : OrderedState.Partial.Block (ThreadedOp (Wires.Effect Φ)) (TyDen (τ := τ)) σ}
    (blocked : abnormal (Wires.model (ε := ε)) g (point (enter input) initial) (.blocked attempt))
    (fuel : Nat) : run actions g fuel input initial = none := by
  let model := Wires.model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)
  let entry := point (enter (A := A) (C := X) (D := Z) input) initial
  cases result : run actions g fuel input initial with
  | none => rfl
  | some output =>
    have finite := (NestedTheta.Partial.Executable.returns_iff actions g entry output).mp ⟨fuel, result⟩
    have returned := (returns_iff model g checked entry output).mp finite
    have stopped := (abnormal_iff model g checked entry (.blocked attempt)).mp blocked
    exact False.elim (OrderedState.Partial.return_excludes_abnormal (erasedModel model) checked.erase.toGraph
      (boundaryResult entry).1 (boundaryResult entry).2 returned (.blocked attempt) stopped)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Proofs
