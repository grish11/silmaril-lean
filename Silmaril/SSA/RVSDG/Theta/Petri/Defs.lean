module

public import Silmaril.SSA.RVSDG.Theta.Defs
public import Silmaril.SSA.RVSDG.Petri.Defs

/-! The θ Petri machine discards each finished body marking and seeds a fresh
one with the updated carried tuple when the continuation predicate is true. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Theta.Petri

universe u v w

open Relation (ReflTransGen)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

inductive Marking (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs) where
  | active (input : Tuple m.Val carried) (body : RVSDG.Petri.GraphMarking m graph.body)
  | returned (output : Tuple m.Val carried)

def initial (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs) (input : Tuple m.Val carried) :
    Marking m graph :=
  .active input (RVSDG.Petri.initial m graph.body)

inductive Step (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs) :
    Marking m graph → Marking m graph → Prop where
  | inside {input : Tuple m.Val carried} {before after : RVSDG.Petri.GraphMarking m graph.body}
      (step : RVSDG.Petri.Step m graph.body input before after) :
      Step m graph (.active input before) (.active input after)
  | again {input next : Tuple m.Val carried} {body : RVSDG.Petri.GraphMarking m graph.body}
      (completed : RVSDG.Petri.result m graph.body input body = some (bodyResult m true next)) :
      Step m graph (.active input body) (initial m graph next)
  | exit {input output : Tuple m.Val carried} {body : RVSDG.Petri.GraphMarking m graph.body}
      (completed : RVSDG.Petri.result m graph.body input body = some (bodyResult m false output)) :
      Step m graph (.active input body) (.returned output)

def Finishes (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    (input output : Tuple m.Val carried) : Prop :=
  ReflTransGen (Step m graph) (initial m graph input) (.returned output)

/-- Divergence observed by infinitely many legal θ restarts. Each checkpoint
includes a complete body firing sequence and one restart to a fresh marking. -/
def Diverges (m : Model.{u, v, w} Op) (graph : Graph Op carried sigs)
    (input : Tuple m.Val carried) : Prop :=
  Repeats (fun before again after => RVSDG.Petri.Finishes m graph.body before (bodyResult m again after))
    input

end Silmaril.SSA.RVSDG.Theta.Petri
