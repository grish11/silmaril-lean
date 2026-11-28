module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport.Transfer

/-! # Transport of normalized LetIter tables with pure transfers

Both endpoints use the transfer-enabled plan renderers. A pure transfer
enters the original-state summand without issuing a request or visiting a
pending-reply state. The joined quotient proof eliminates the pending
block with `iterateChosen_bypass`.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Transfer

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B : Code}

local notation "Ops" => Opcode F

open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect AbortEquiv)

theorem fused_lowers (t : Rows F S B S) :
    (TransferPlans.source t.plans).toLetIter 1 = some (t.fused.native 0) :=
  RequestBlockTransport.Proofs.Transfer.fused_lowers t

theorem expanded_lowers (t : Rows F S B S) :
    (TransferPlans.expand t.plans).source.toLetIter 1 = some (t.expanded.native 0) :=
  RequestBlockTransport.Proofs.Transfer.expanded_lowers t

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε]
variable [EffectIteration ε] {e : ε}
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Exact transport for normalized tables with pure transfers. -/
theorem endpoint_transport (t : Rows F S B S) (init : S.Value)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    HasTypeEffect Free .nil (fusedLoop t init) B.ty e ∧
    HasTypeEffect Free .nil (expandedLoop t init) B.ty e ∧
    AbortEquiv (⊥ : ε) Free .nil (fusedLoop t init) (expandedLoop t init) B.ty ∧
    ∃ (r s : Region Ops), eraseLoop S (fusedLoop t init) = some r ∧
      eraseLoop (.sum S t.pending) (expandedLoop t init) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [B.ty] ∧
      Region.ValueBranches [Code.unit.ty] s [B.ty] ∧
      Region.Paper.Extension.Eqv (targetSeed (⊥ : ε)) [Code.unit.ty] r s [B.ty] :=
  RequestBlockTransport.Proofs.Transfer.endpoint_transport t init hf he

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Transfer
