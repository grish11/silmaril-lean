module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport

/-! # Transport of the normalized one-state LetIter subdivision

The original state consists of one unit code. The first request uses a
closed constructor argument, and each reply selects a one-request row
or an immediate return. The argument, reply, and result codes are built
from unit and sums. Both endpoints use the supplied iterative effect
bound. Their native equation is `Plans.expand_eq`, and equality of the
translated CFGs follows from the typed request-block law in the joined
singleton quotient.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

open Silmaril.Isotope.LetIter.LocallyNameless (HasTypeEffect AbortEquiv)

variable {O : Code}

theorem fused_lowers (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) :
    (plans f x k).source.toLetIter 1 = some ((fused f x k).native 0) :=
  Proofs.fused_lowers f x k

theorem expanded_lowers (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O) :
    (plans f x k).expand.source.toLetIter 1 = some ((expanded f x k).native 0) :=
  Proofs.expanded_lowers f x k

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε}

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- The computed #3846 native endpoints have the supplied effect bound,
are related by native AbortEquiv, and erase to equal typed LambdaSSA CFGs. -/
theorem endpoint_transport (f : Ops) (x : f.argCode.Value) (k : f.replyCode.Value → Row F U O)
    (hf : ∀ p : Ops, instrEff p ≤ e) (he : IsIterative e) :
    HasTypeEffect Free .nil (fusedNative f x k) O.ty e ∧
    HasTypeEffect Free .nil (expandedNative f x k) O.ty e ∧
    AbortEquiv (⊥ : ε) Free .nil (fusedNative f x k) (expandedNative f x k) O.ty ∧
    ∃ (r s : Region Ops), eraseLoop U (fusedNative f x k) = some r ∧
      eraseLoop (.sum U f.replyCode) (expandedNative f x k) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [O.ty] ∧ Region.ValueBranches [Code.unit.ty] s [O.ty] ∧
      Region.Paper.Extension.Eqv (targetSeed (⊥ : ε)) [Code.unit.ty] r s [O.ty] :=
  Proofs.endpoint_transport f x k hf he

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
