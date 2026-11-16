module

public import Silmaril.Logic.Institution.Basic

@[expose] public section

/-! # Normal modal K: pointed Kripke semantics
Atom-renaming signatures, unrestricted frames and bounded model morphisms.
Reflexivity/transitivity/symmetry are additional frame conditions, not K axioms.
-/

namespace Silmaril.Logic.Modal
open CategoryTheory Silmaril.Logic.Institution

structure Signature : Type 1 where
  Atom : Type

instance : Category Signature where
  Hom S T := S.Atom → T.Atom
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

inductive Formula (S : Signature) where
  | atom : S.Atom → Formula S
  | bot : Formula S
  | imp : Formula S → Formula S → Formula S
  | box : Formula S → Formula S

def Formula.map {S T : Signature} (f : S ⟶ T) : Formula S → Formula T
  | .atom a => .atom (f a)
  | .bot => .bot
  | .imp p q => .imp (p.map f) (q.map f)
  | .box p => .box (p.map f)

/-- A pointed model; empty frames are excluded by the distinguished world. -/
structure Model (S : Signature) : Type 1 where
  World : Type
  accessible : World → World → Prop
  valuation : S.Atom → World → Prop
  point : World

/-- Bounded morphisms preserve points, atom truth, and both directions of accessibility. -/
structure Model.Hom {S : Signature} (M N : Model S) where
  map : M.World → N.World
  point : map M.point = N.point
  atoms : ∀ a w, M.valuation a w ↔ N.valuation a (map w)
  forth : ∀ w v, M.accessible w v → N.accessible (map w) (map v)
  back : ∀ w v, N.accessible (map w) v → ∃ u, M.accessible w u ∧ map u = v

instance (S : Signature) : Category (Model S) where
  Hom := Model.Hom
  id M := ⟨id, rfl, fun _ _ => Iff.rfl, fun _ _ h => h, fun _ v h => ⟨v, h, rfl⟩⟩
  comp f g :=
    { map := g.map ∘ f.map
      point := by change g.map (f.map _) = _; rw [f.point, g.point]
      atoms := fun a w => (f.atoms a w).trans (g.atoms a (f.map w))
      forth := fun w v h => g.forth _ _ (f.forth w v h)
      back := by
        intro w v h
        obtain ⟨u, hu, huv⟩ := g.back (f.map w) v h
        obtain ⟨t, ht, htu⟩ := f.back w u hu
        exact ⟨t, ht, by change g.map (f.map t) = v; rw [htu, huv]⟩ }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def Formula.Holds {S : Signature} (M : Model S) : Formula S → M.World → Prop
  | .atom a, w => M.valuation a w
  | .bot, _ => False
  | .imp p q, w => p.Holds M w → q.Holds M w
  | .box p, w => ∀ v, M.accessible w v → p.Holds M v

def Sat {S : Signature} (M : Model S) (p : Formula S) : Prop := p.Holds M M.point

/-- Atom reduct preserves the frame and its distinguished point. -/
def reduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj M := ⟨M.World, M.accessible, fun a => M.valuation (f a), M.point⟩
  map h := ⟨h.map, h.point, fun a w => h.atoms (f a) w, h.forth, h.back⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.Modal
