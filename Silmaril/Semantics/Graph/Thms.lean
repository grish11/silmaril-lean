module

public import Silmaril.Semantics.Graph.Defs
import Silmaril.Proofs.Semantics.Graph.Basic

@[expose] public section
namespace Silmaril.Semantics.Graph
universe u v

def Iso.symm {V : Type u} {W : Type v} {g : RelGraph V} {h : RelGraph W} (f : Iso g h) : Iso h g :=
  ⟨f.vertices.symm, fun a b => by
    simpa using (f.edge_iff (f.vertices.symm a) (f.vertices.symm b)).symm⟩

theorem Minor.exists_refl {V : Type u} (g : RelGraph V) : Nonempty (Minor g g) := ⟨Proofs.minor_refl g⟩

noncomputable def Minor.refl {V : Type u} (g : RelGraph V) : Minor g g :=
  Classical.choice (Minor.exists_refl g)

theorem Minor.exists_of_iso {V : Type u} {W : Type v} {g : RelGraph V} {h : RelGraph W}
    (f : Iso g h) : Nonempty (Minor g h) := ⟨Proofs.minor_of_iso f⟩

noncomputable def Iso.minor {V : Type u} {W : Type v} {g : RelGraph V} {h : RelGraph W}
    (f : Iso g h) : Minor g h := Classical.choice (Minor.exists_of_iso f)

theorem undirected_symmetric {V : Type u} (g : RelGraph V) (a b : V) :
    g.undirected.edge a b → g.undirected.edge b a := fun ⟨hne, h⟩ => ⟨Ne.symm hne, h.symm⟩

theorem undirected_no_loop {V : Type u} (g : RelGraph V) (a : V) : ¬ g.undirected.edge a a :=
  fun h => h.1 rfl

end Silmaril.Semantics.Graph
