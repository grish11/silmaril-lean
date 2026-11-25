module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Defs

/-! # A source case over the newest input slot -/

@[expose] public section

open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case

universe v

/-- Each arm is written with its payload at index zero and the ambient
inputs after it. Weaken the arm below the payload to insert the scrutinee slot. -/
def onHead {Φ : Type v} (left right : Expr Φ) : Expr Φ :=
  .case (.var 0) left.wk1 right.wk1

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case
