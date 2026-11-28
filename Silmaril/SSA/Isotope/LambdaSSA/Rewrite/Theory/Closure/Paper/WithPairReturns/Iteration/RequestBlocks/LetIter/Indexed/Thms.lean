module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Indexed.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport.Indexed

/-! # Typed transport of the indexed LetIter request subdivision

Every original state begins with a request. Its reply determines a second
request or an immediate return. The pending-state code stores each original
state's own reply type. A second reply may transfer control to any original state.

The native endpoints are the lowerings of `Plans.source` and
`Plans.expand` at the supplied effect bound. Their LambdaSSA translations
agree by the typed request-block law in `WithPairReturns.JoinedStep`.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Indexed

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {I S B : Code}

local notation "Ops" => Opcode F

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect AbortEquiv)

variable {ε : Type} [HasEff (Opcode F) ε]

/-- Factor the fused table through the exact syntax type of its indexed
pending replies. -/
theorem factor (pe : ε) (t : Rows F S B I) :
    t.first.arrow pe ≫ t.second.arrow pe = t.fused.arrow pe :=
  RequestBlockTransport.Proofs.Indexed.factor pe t

theorem fused_lowers (t : Rows F S B S) :
    (Plans.source t.plans).toLetIter 1 = some (t.fused.native 0) :=
  RequestBlockTransport.Proofs.Indexed.fused_lowers t

theorem expanded_lowers (t : Rows F S B S) :
    (Plans.expand t.plans).source.toLetIter 1 = some (t.expanded.native 0) :=
  RequestBlockTransport.Proofs.Indexed.expanded_lowers t

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Both endpoints are the #3846 lowerings at the same supplied bound.
The joined equality comes from the factorization through the indexed
pending-reply code and the request-block iteration law. -/
theorem endpoint_transport (t : Rows F S B S) (init : S.Value)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) :
    HasTypeEffect Free .nil (fusedNative t init) B.ty e ∧
    HasTypeEffect Free .nil (expandedNative t init) B.ty e ∧
    AbortEquiv (⊥ : ε) Free .nil (fusedNative t init) (expandedNative t init) B.ty ∧
    ∃ (r s : Region Ops), eraseLoop S (fusedNative t init) = some r ∧
      eraseLoop (.sum S t.pending) (expandedNative t init) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [B.ty] ∧
      Region.ValueBranches [Code.unit.ty] s [B.ty] ∧
      Region.Paper.Extension.Eqv (targetSeed (⊥ : ε)) [Code.unit.ty] r s [B.ty] :=
  RequestBlockTransport.Proofs.Indexed.endpoint_transport t init hf he

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Indexed
