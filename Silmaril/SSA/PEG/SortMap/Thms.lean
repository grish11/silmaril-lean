module

public import Silmaril.SSA.PEG.SortMap.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.SortMap.Structure
import Silmaril.Proofs.SSA.PEG.SortMap.Functorial
import Silmaril.Proofs.SSA.PEG.SortMap.Semantics

/-! # Structural laws for heterogeneous PEG signature transport -/

public section

namespace Silmaril.SSA.PEG

open RVSDG (Tuple)

universe u u' u'' v v' v'' w

variable {D : Type u} {E : Type u'} {f : D → E}
variable {P : InstructionSet.{u,v} D} {Q : InstructionSet.{u',v'} E}
variable {params results : List (Ty D)} {n l : Nat}

/-- Each numbered edge and its exact role is preserved and reflected. -/
theorem Graph.edge_mapData (g : Graph P params results n l) (op : ProfileMap f P Q)
    (a b : Fin n) (role : EdgeKind (Fin l)) :
    (g.mapData op).Edge a role b ↔ g.Edge a role b := SortMapProofs.edge op g a b role

/-- Requests retain their vertex number and index, including feedback and sample demands. -/
theorem Graph.demand_mapData (g : Graph P params results n l) (op : ProfileMap f P Q)
    (p q : Request n l) : (g.mapData op).Demand p q ↔ g.Demand p q := SortMapProofs.demand op g p q

theorem Graph.demandWellFounded_mapData (g : Graph P params results n l) (op : ProfileMap f P Q) :
    WellFounded (g.mapData op).Demand ↔ WellFounded g.Demand :=
  SortMapProofs.demandWellFounded op g

theorem Graph.wellFormed_mapData (g : Graph P params results n l) (op : ProfileMap f P Q) :
    (g.mapData op).WellFormed ↔ g.WellFormed := SortMapProofs.wellFormed op g

/-- An identity sort map agrees with ordinary opcode relabeling, after aligning
the two ordered boundary lists. -/
theorem Graph.mapData_fixed {Q : InstructionSet.{u,v'} D}
    (g : Graph P params results n l) (op : InstructionMap P Q) :
    HEq (g.mapData (ProfileMap.fixed (P := P) (Q := Q) op)) (g.mapOps op) :=
  SortMapProofs.graph_fixed op g

theorem Graph.mapData_id (g : Graph P params results n l) :
    HEq (g.mapData (ProfileMap.fixed (P := P) (Q := P) (fun x => x))) g :=
  (g.mapData_fixed (Q := P) (fun x => x)).trans (heq_of_eq g.mapOps_id)

theorem Graph.mapData_comp {F : Type u''} {h : E → F} {R : InstructionSet.{u'',v''} F}
    (g : Graph P params results n l) (op : ProfileMap f P Q) (next : ProfileMap h Q R) :
    HEq ((g.mapData op).mapData next) (g.mapData (ProfileMap.comp op next)) :=
  SortMapProofs.graph_comp op next g

theorem Interpretation.reductData_fixed {Q : InstructionSet.{u,v'} D}
    (m : Interpretation.{u,v',w} Q) (op : InstructionMap P Q) :
    m.reductData (ProfileMap.fixed (P := P) (Q := Q) op) = m.reduct op :=
  SortMapProofs.reduct_fixed op m

theorem Interpretation.reductData_comp {F : Type u''} {h : E → F} {R : InstructionSet.{u'',v''} F}
    (m : Interpretation.{u'',v'',w} R) (op : ProfileMap f P Q) (next : ProfileMap h Q R) :
    m.reductData (ProfileMap.comp op next) = (m.reductData next).reductData op :=
  SortMapProofs.reduct_comp op next m

variable (g : Graph P params results n l) (op : ProfileMap f P Q)
variable (m : Interpretation.{u',v',w} Q) (input : Tuple (m.reductData op).Value params)

/-- Transport every node equation under the pullback model, including bottom. -/
theorem Graph.equation_mapData (v : g.Valuation (m.reductData op)) (q : Request n l) :
    (g.mapData op).equation m (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input)
      (g.mapDataValuation op m v) q =
      (g.equation (m.reductData op) input v q).map (Ty.valueMapEquiv f m.carrier (g.sort q.1)) :=
  SortMapProofs.equation op m g input v q

theorem Graph.denote_mapData (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapData op).Demand) :
    (g.mapData op).denote m (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input) mapped =
      g.mapDataValuation op m (g.denote (m.reductData op) input wf) :=
  SortMapProofs.denote op m g input wf mapped

theorem Graph.observe_denote_mapData (i : Index l)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapData op).Demand) :
    (g.mapData op).observe m ((g.mapData op).denote m
      (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input) mapped) i =
      mapDataTuple f (fun t x => x.map (Ty.valueMapEquiv f m.carrier t))
        (g.observe (m.reductData op) (g.denote (m.reductData op) input wf) i) :=
  SortMapProofs.observe op m g input i wf mapped

end Silmaril.SSA.PEG
