module

public import Silmaril.SSA.PEG.Figure19.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Figure19.Boundary

public section

namespace Silmaril.SSA.PEG.Figure19

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {depth : Fin l → Nat}
variable {direction : EvalDirection} {cap : Nat} {ctx : Assumptions n} {i : Fin n}

theorem Derives.evalBoundary (typed : Derives g depth direction cap ctx i) :
    EvalBoundary g depth direction cap i :=
  Proofs.evalBoundary typed

/-- The literal printed arrow cannot type a directly designated eval
at depth zero, even with Type-Reduce. -/
theorem CFGContext.printed_no_root_eval (typed : CFGContext g depth .printed)
    (slot : Fin results.length) {key : Fin l}
    {args : Tuple (Ref g.sort) [g.sort (g.roots.get (portAt results slot)).id, .count]}
    (row : g.node (g.roots.get (portAt results slot)).id = .ofLabel (.eval key) args) : False :=
  Proofs.printed_no_root_eval typed slot row

theorem Guarded.demandWellFounded (a : Guarded g direction) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.rank a.ranked

end Silmaril.SSA.PEG.Figure19
