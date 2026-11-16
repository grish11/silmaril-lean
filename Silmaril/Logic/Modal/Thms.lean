module

public import Silmaril.Logic.Modal.Defs
public import Silmaril.Logic.Institution.Morphism

@[expose] public section

namespace Silmaril.Logic.Modal
open CategoryTheory Silmaril.Logic.Institution

theorem Formula.map_id {S : Signature} (p : Formula S) : p.map (𝟙 S) = p := by
  induction p with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => simp only [Formula.map, hp, hq]
  | box p hp => simp only [Formula.map, hp]

theorem Formula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (p : Formula S) : p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => simp only [Formula.map, hp, hq]
  | box p hp => simp only [Formula.map, hp]

/-- Truth is invariant under actual bounded morphisms, at every world. -/
theorem Formula.holds_hom {S : Signature} {M N : Model S} (h : M ⟶ N)
    (p : Formula S) (w : M.World) : p.Holds M w ↔ p.Holds N (h.map w) := by
  induction p generalizing w with
  | atom a => exact h.atoms a w
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp w) (hq w)
  | box p hp =>
    constructor
    · intro hm v hv
      obtain ⟨u, hu, rfl⟩ := h.back w v hv
      exact (hp u).mp (hm u hu)
    · intro hn v hv
      exact (hp v).mpr (hn (h.map v) (h.forth w v hv))

/-- Point preservation lifts bounded-morphism invariance to satisfaction. -/
theorem sat_hom {S : Signature} {M N : Model S} (h : M ⟶ N) (p : Formula S) :
    Sat M p ↔ Sat N p := by
  unfold Sat
  rw [p.holds_hom h, h.point]

/-- Signature renaming and valuation reduct obey the satisfaction condition. -/
theorem Formula.holds_map {S T : Signature} (f : S ⟶ T) (M : Model T)
    (p : Formula S) (w : M.World) : (p.map f).Holds M w ↔ p.Holds ((reduct f).obj M) w := by
  induction p generalizing w with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp w) (hq w)
  | box p hp => exact forall_congr' fun v => imp_congr_right fun _ => hp v

def institution : Signature ⥤ Room where
  obj S := ⟨Formula S, Cat.of (Model S), Sat⟩
  map f := ⟨Formula.map f, reduct f, fun M p => p.holds_map f M M.point⟩
  map_id _ := Room.hom_ext (funext Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Formula.map_comp f g)) rfl

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

/-- The distribution axiom K holds on every frame. -/
theorem axiom_K {S : Signature} (M : Model S) (p q : Formula S) (w : M.World) :
    (Formula.imp (.box (.imp p q)) (.imp (.box p) (.box q))).Holds M w := by
  intro hpq hp v hv
  exact hpq v hv (hp v hv)

/-- Validity ranges over all models and all worlds. -/
def Valid {S : Signature} (p : Formula S) : Prop := ∀ M : Model S, ∀ w, p.Holds M w

/-- Necessitation requires validity, rather than truth at a single world. -/
theorem necessitation {S : Signature} {p : Formula S} (h : Valid p) : Valid (.box p) := by
  intro M w v _
  exact h M v

/-- T requires reflexive frames; it is not assumed by K. -/
theorem axiom_T_of_reflexive {S : Signature} (M : Model S)
    (hreflexive : ∀ w, M.accessible w w) (p : Formula S) (w : M.World) :
    (Formula.imp (.box p) p).Holds M w := fun h => h w (hreflexive w)

end Silmaril.Logic.Modal
