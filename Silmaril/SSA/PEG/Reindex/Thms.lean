module

public import Silmaril.SSA.PEG.Reindex.Defs
public import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n n' l l' : Nat}
variable {old : Graph P params results n l} {new : Graph P params results n' l'}
variable {rows : Fin n' ≃ Fin n} {loops : Fin l' ≃ Fin l}

theorem Graph.ReindexCertificate.graph_eq [DecidableEq Data]
    (cert : old.ReindexCertificate new rows loops) : old.reindex rows loops = new :=
  Graph.eq_of_toRaw_eq cert.table

theorem Graph.ReindexCertificate.wellFormed_iff [DecidableEq Data]
    (cert : old.ReindexCertificate new rows loops) : new.WellFormed ↔ old.WellFormed :=
  cert.graph_eq ▸ old.wellFormed_reindex rows loops

end Silmaril.SSA.PEG
