module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Mixed.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport.Transfer

/-! # Transport of mixed normalized LetIter tables

An original state can run a direct row or issue the first request of a
two-request row. A direct row follows the original return-or-repeat control
type. A two-request row enters the pending state for its first reply.

Both endpoints use the original `Plans.source` and `Plans.expand` renderers
at the supplied iterative bound. A bare pure transfer is well-typed as
LetIter syntax. Its lowering is outside the image of the original
`Plan` grammar, as witnessed by `typed_transfer_unrendered`.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Mixed

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
    (Plans.source t.plans).toLetIter 1 = some (t.fused.native 0) :=
  RequestBlockTransport.Proofs.Transfer.legacy_fused_lowers t

theorem expanded_lowers (t : Rows F S B S) :
    (Plans.expand t.plans).source.toLetIter 1 = some (t.expanded.native 0) :=
  RequestBlockTransport.Proofs.Transfer.legacy_expanded_lowers t

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε]

/-- The missing row is well-typed even below top. The obstruction is
the normalized renderer's row grammar. -/
theorem typed_transfer_unrendered (e : ε) (t : S.Value) :
    Wf [(S.ty, (⊥ : ε))] (.inr (S.literal t) : Expr Ops) (Code.sum B S).ty e ∧
    ∀ p : Plan F S B, p.source.toLetIter 1 ≠ (Expr.inr (S.literal t) : Expr Ops).toLetIter 1 :=
  RequestBlockTransport.Proofs.Transfer.typed_transfer_unrendered e t

variable [EffectIteration ε] {e : ε}
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Exact transport for mixed normalized tables using both #3846 plan forms. -/
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
  RequestBlockTransport.Proofs.Transfer.endpoint_transport t.withTransfers init hf he

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Mixed
