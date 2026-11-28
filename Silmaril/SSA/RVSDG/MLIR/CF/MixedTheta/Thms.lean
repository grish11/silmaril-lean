module

public import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Defs
import Silmaril.Proofs.SSA.RVSDG.MLIR.CF.MixedTheta.Correctness

public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta

open Silmaril.MLIR.Arith (Env Width)
open LambdaSSA.Acyclic.Theta.Translation
open LambdaSSA.OrderedTheta (point)
open Isotope.LetIter.ProofRelevant.Semantics

variable {τ Φ ε σ : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{0,0} τ] [InstructionModel Φ τ ε (StateT σ Part)]
variable {A : τ} {w : Width} {g : PureTheta.Reverse.Graph Φ ε A}

/-- The emitted body evaluates one source step, before CF selects its successor. -/
theorem activation_result (codec : TyDen A ≃ BitVec w.val) (s : PureTheta.Loop Φ ε A)
    (pureFirst : Bool) (input : Env [w]) (x : TyDen A) :
    eval (σ := σ) codec (activation s pureFirst) ((packet codec x).append input) =
      (s.step (σ := σ) x >>= fun route => pure (activationPacket codec route)) :=
  Proofs.activation_result codec s pureFirst input x

/-- The generated ordered CF program returns the encoded carry and exact
final store at some finite bound precisely when the input numbered graph
observes that value and live token. A fuel-exhausted result supplies no
return witness. -/
theorem returns_iff (codec : TyDen A ≃ BitVec w.val) (f : PureTheta.Reverse.Fibre g)
    (input output : TyDen A) (initial final : σ) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ)) g (point input initial) =
        Part.some (point output final) ↔
      ∃ fuel, ((lower w f).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
        Part.some (some (packet codec output), final) :=
  Proofs.returns_iff codec f input output initial final

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta
