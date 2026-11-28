module

public import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Defs
import Silmaril.Proofs.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Correctness

public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (i1)
open LambdaSSA.Acyclic.Theta
open LambdaSSA.Acyclic.Theta.Translation
open LambdaSSA.OrderedTheta (point)
open Silmaril.Elgot (iter)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)

variable {τ Φ ε σ : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{0,0} τ] [InstructionModel Φ τ ε (StateT σ Part)]
variable {A : τ} {w : Width} {g : Graph Φ ε A}

/-- On the source side, the recovered carrier conversion passes the
producer's completed payload and token to the continuation. -/
theorem observe_eq_bind (f : Admission g) (input : TyDen A) (initial : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) =
      ((iter (f.recovered.shape.loop.step (σ := σ)) input).run initial).bind (fun (mid, token) =>
        Part.map (ExplicitRuntime.exitTuple (A := A))
          ((iter (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) f.leaf.loop) mid).run token)) :=
  Proofs.observe_splice f input initial

/-- Successful runs of the emitted splice agree with the original numbered
table on both exit labels, their carry, and the exact final store. -/
theorem returns_iff (codec : TyDen A ≃ BitVec w.val) (f : Admission g)
    (input : TyDen A) (initial : σ) (label : LabelDen [A,A]) (final : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) =
      Part.some (ExplicitRuntime.exitTuple (A := A) (label, final)) ↔
    ∃ fuel, ((lower w f).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
      Part.some (some (exitPacket codec label), final) :=
  Proofs.returns_iff f codec input initial label final

/-- A source observation is undefined exactly when no budget can return a
target packet and store. An exhausted budget can still report its store. -/
theorem no_return_iff (codec : TyDen A ≃ BitVec w.val) (f : Admission g)
    (input : TyDen A) (initial : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) = Part.none ↔
    ∀ (output : Env [i1,w]) (final : σ), ¬ ∃ fuel,
      ((lower w f).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
        Part.some (some output, final) :=
  Proofs.no_return_iff f codec input initial

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix
