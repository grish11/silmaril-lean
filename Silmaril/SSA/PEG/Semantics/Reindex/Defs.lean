module

public import Silmaril.SSA.PEG.Semantics.Defs

/-! # Coordinate transport for PEG renumberings

As in `Graph.reindex`, each equivalence maps new identifiers to old
identifiers. Indices pull back along the loop equivalence. -/

@[expose] public section

namespace Silmaril.SSA.PEG

universe u v w

variable {n n' l l' : Nat}
variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)}

def Index.reindex (i : Index l) (loops : Fin l' ≃ Fin l) : Index l' :=
  i ∘ loops

/-- Interpret a request in the old numbering. -/
def Request.toOriginal (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l)
    (q : Request n' l') : Request n l :=
  (rows q.1, q.2.reindex loops.symm)

def RankComponent.reindex (c : RankComponent n l)
    (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) : RankComponent n' l' :=
  match c with
  | .phase height => .phase (height ∘ rows)
  | .counter key => .counter (loops.symm key)

def DemandRank.reindex (rank : DemandRank n l)
    (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) : DemandRank n' l' :=
  rank.map fun c => c.reindex rows loops

/-- Transport every typed node value, including bottom. The row sort in
the new table is definitionally the sort at the original address. -/
def Graph.reindexValuation (g : Graph P params results n l) (m : Interpretation.{u,v,w} P)
    (rows : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l)
    (values : g.Valuation m) : (g.reindex rows loops).Valuation m :=
  fun q => values (Request.toOriginal rows loops q)

end Silmaril.SSA.PEG
