module

public import Silmaril.SSA.MLIR.Institution.Defs

/-! Sentence translation and model restriction along the inclusion of regionless signatures. -/

@[expose] public section

namespace Silmaril.MLIR.Institution

variable {S : Signature false}

/-- Read a regionless term in the larger syntax, preserving its typing context. -/
def Term.withRegions {n : Nat} {Γ : Fin n → S.Ty} {s : S.Ty} :
    Term S Γ s → Term (Signature.withRegions.obj S) Γ s
  | .var i => .var i
  | .app (a := a) (p := p) o args bodies i =>
    Term.app (S := Signature.withRegions.obj S) (a := a.withRegions) (p := p.withRegions)
      (Signature.RegionlessOp.lift o)
      (fun j => (args j).withRegions) (fun r j => (bodies r j).withRegions) i

/-- The same typed equation in the syntax that allows isolated regions. -/
def Equation.withRegions (e : Equation S) : Equation (Signature.withRegions.obj S) where
  inputs := e.inputs
  outputs := e.outputs
  context := e.context
  results := e.results
  lhs i := (e.lhs i).withRegions
  rhs i := (e.rhs i).withRegions

/-- Restrict a model of a lifted signature to its regionless presentation. -/
def Model.restrictRegionless (M : Model (Signature.withRegions.obj S)) : Model S where
  carrier := M.carrier
  op o := M.op (.lift o)

end Silmaril.MLIR.Institution
