module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Binders.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Variables.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open Uflia.SExpr Uflia.Quantified.SExpr

/-- Equality transport changes only the open context, retaining the inferred sort. -/
def castPacked {E : Environment} {k : Nat} {Γ Δ : Fin k → SortCode String}
    (h : Γ = Δ) (value : PackedTerm E Γ) : PackedTerm E Δ :=
  ⟨value.sort, cast (congrArg (fun ctx => Uflia.Quantified.Term E.signature ctx value.sort) h) value.term⟩

def castLocals {E : Environment} {k : Nat} {Γ Δ : Fin k → SortCode String}
    (h : Γ = Δ) (locals : Uflia.Quantified.SExpr.Locals E Γ) :
    Uflia.Quantified.SExpr.Locals E Δ :=
  locals.map (fun entry => (entry.1, castPacked h entry.2))

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
