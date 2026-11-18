module

public import Silmaril.Semantics.Graph.Defs

@[expose] public section
namespace Silmaril.Semantics.Graph.Proofs
universe u v

def minor_refl {V : Type u} (g : RelGraph V) : Minor g g := by
  refine ⟨fun v => {v}, fun v => ⟨v, rfl⟩, ?_, ?_, ?_⟩
  · intro a b h
    exact Set.disjoint_left.mpr (fun x ha hb => h (ha.symm.trans hb))
  · intro v a ha b hb
    have : a = v := ha
    have : b = v := hb
    subst a; subst b
    exact .refl
  · intro a b h
    exact ⟨a, rfl, b, rfl, h⟩

def minor_of_iso {V : Type u} {W : Type v} {g : RelGraph V} {h : RelGraph W}
    (f : Iso g h) : Minor g h := by
  refine ⟨fun v => {f.vertices v}, fun v => ⟨f.vertices v, rfl⟩, ?_, ?_, ?_⟩
  · intro a b hne
    exact Set.disjoint_left.mpr (fun x ha hb => hne (f.vertices.injective (ha.symm.trans hb)))
  · intro v a ha b hb
    have : a = f.vertices v := ha
    have : b = f.vertices v := hb
    subst a; subst b
    exact .refl
  · intro a b edge
    refine ⟨f.vertices a, rfl, f.vertices b, rfl, ?_, ?_⟩
    · exact fun eq => edge.1 (f.vertices.injective eq)
    · exact edge.2.imp ((f.edge_iff a b).mpr) ((f.edge_iff b a).mpr)

end Silmaril.Semantics.Graph.Proofs
