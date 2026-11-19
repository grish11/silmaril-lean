module

public import Silmaril.Logic.Graph.Thms
public import Silmaril.Logic.Graph.Incidence.Thms
public import Silmaril.Semantics.Graph.Thms

@[expose] public section
namespace Silmaril.Logic.Graph.Examples
open CategoryTheory

def one : Signature := ⟨Unit⟩
def two : Signature := ⟨Bool⟩
def collapse : two ⟶ one := ⟨fun _ => ()⟩
def withoutLoop : PresentModel one := ⟨Set.univ, ⟨fun _ _ => False⟩⟩
def withLoop : PresentModel one := ⟨Set.univ, ⟨fun _ _ => True⟩⟩

def parallel : Incidence.Signature := ⟨Unit, Bool, fun _ => some (), fun _ => some ()⟩
def oneEdge : Incidence.Model parallel := ⟨Set.univ, {false}⟩
def twoEdges : Incidence.Model parallel := ⟨Set.univ, Set.univ⟩

def incomplete : Incidence.Signature := ⟨Unit, Unit, fun _ => none, fun _ => some ()⟩
def unknownEdge : Incidence.Model incomplete := ⟨Set.univ, Set.univ⟩
def noEdge : Incidence.Model incomplete := ⟨Set.univ, ∅⟩

/-- Cross-base isomorphism: vertex types differ, adjacency is transported exactly. -/
def namedGraph : Silmaril.Semantics.Graph.RelGraph Bool := ⟨fun a b => a = false ∧ b = true⟩
def indexedGraph : Silmaril.Semantics.Graph.RelGraph (Fin 2) := ⟨fun a b => a = 0 ∧ b = 1⟩

/-- An iteration includes the backedge, not just containment arcs. -/
def iteration : Silmaril.Semantics.Graph.Structured Nat := .iteration 0 3 (.edge 1 2)

end Silmaril.Logic.Graph.Examples
