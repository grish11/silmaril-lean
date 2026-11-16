module

public import Silmaril.Proofs.Logic.CTL.Semantics

@[expose] public section
namespace Silmaril.Logic.CTL
open CategoryTheory Silmaril.Logic.Institution

def institution : Signature ⥤ Room where
  obj S := ⟨Formula S, Cat.of (Model S), Sat⟩
  map f := ⟨Formula.map f, modelReduct f, fun M p => p.holds_map f M M.toModal.point⟩
  map_id _ := Room.hom_ext (funext Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Formula.map_comp f g)) rfl

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)

/-- K's box is the weak next dual, preserving K's deadlock convention. -/
def encodeK {S : Signature} : Modal.Formula S → Formula S
  | .atom a => .atom a
  | .bot => .bot
  | .imp p q => .imp (encodeK p) (encodeK q)
  | .box p => .ax (encodeK p)

def kModels (S : Signature) : Model S ⥤ Modal.Model S where
  obj := Model.toModal
  map h := eqToHom (congrArg Model.toModal h.down)
  map_id _ := rfl
  map_comp f g := by cases f.down; cases g.down; rfl

theorem encodeK_holds {S : Signature} (M : Model S) (p : Modal.Formula S) :
    ∀ w, (encodeK p).Holds M w ↔ p.Holds M.toModal w := by
  classical
  induction p with
  | atom => intro w; rfl
  | bot => intro w; rfl
  | imp p q hp hq =>
      intro w
      change (¬ (¬ ¬ (encodeK p).Holds M w ∧ ¬ (encodeK q).Holds M w)) ↔ _
      rw [hp, hq]
      tauto
  | box p hp =>
      intro w
      change (¬ ∃ v, M.toModal.accessible w v ∧ ¬ (encodeK p).Holds M v) ↔ _
      simp only [hp, not_exists, not_and, not_not]
      rfl

theorem encodeK_map {S T : Signature} (f : S ⟶ T) (p : Modal.Formula S) :
    encodeK (p.map f) = (encodeK p).map f := by
  induction p <;> simp_all [encodeK, Modal.Formula.map, Formula.map, Formula.imp, Formula.disj, Formula.ax]

def kNatural : Modal.institution ⟶ (𝟭 Signature) ⋙ institution where
  app S := ⟨encodeK, kModels S, fun M p => encodeK_holds M p M.toModal.point⟩
  naturality := by
    intro S T f
    apply Room.hom_ext (funext (encodeK_map f))
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro M N h
    cases h.down
    rfl

def kToCTL : Inst.CoHom ⟨Modal.Signature, Modal.institution⟩ ⟨Signature, institution⟩ :=
  ⟨𝟭 _, kNatural⟩

theorem kToCTL_modelExpansive : kToCTL.ModelExpansive := fun _ M => ⟨⟨M⟩, rfl⟩

theorem k_entails_iff (S : Signature) (H : Set (Modal.Formula S)) (p : Modal.Formula S) :
    (Modal.institution.obj S).Entails H p ↔
      (institution.obj S).Entails (encodeK '' H) (encodeK p) :=
  kToCTL.entails_iff kToCTL_modelExpansive S H p

end Silmaril.Logic.CTL
