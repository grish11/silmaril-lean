module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion

/-! # Native iteration with reply-selected substates -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B : Code} {ε : Type} [HasEff (Opcode F) ε] {pe : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))

/-- Split the finite two-request renderer by native uniformity and
codiagonal. The original initializer enters the original-state summand. -/
theorem Plans.expand_eq (M : Plans F S B) (s : S.Value) {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (ha' : (M.stateCode.literal (.inl s)).toLetIter 0 = some a')
    (hb' : M.expand.source.toLetIter 1 = some b') :
    AbortEquiv pe Free .nil (.iter a b) (.iter a' b') B.ty :=
  TerminalProofs.expand_eq M s ha hb ha' hb'

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
