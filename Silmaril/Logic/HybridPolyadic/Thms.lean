module

public import Silmaril.Logic.HybridPolyadic.Defs
import Silmaril.Proofs.Logic.HybridPolyadic.Semantics

@[expose] public section
namespace Silmaril.Logic.HybridPolyadic
open CategoryTheory Silmaril.Logic.Institution

namespace Formula

theorem map_id {S : Signature} {n : ℕ} (p : Formula S n) : p.map (𝟙 S) = p := by
  induction p with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact congrArg₂ Formula.imp hp hq
  | nominal _ => rfl
  | state _ => rfl
  | atNom a p hp => exact congrArg (Formula.atNom a) hp
  | atState i p hp => exact congrArg (Formula.atState i) hp
  | dia a ps ih => exact congrArg (Formula.dia a) (funext ih)
  | down p hp => exact congrArg Formula.down hp

theorem map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) {n : ℕ}
    (p : Formula S n) : p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact congrArg₂ Formula.imp hp hq
  | nominal _ => rfl
  | state _ => rfl
  | atNom a p hp => exact congrArg (Formula.atNom _) hp
  | atState i p hp => exact congrArg (Formula.atState i) hp
  | dia a ps ih => exact congrArg (Formula.dia _) (funext ih)
  | down p hp => exact congrArg Formula.down hp

/-- Capture-avoiding scope renaming is interpreted by environment precomposition. -/
theorem holds_rename {S : Signature} (M : Model S) {n m : ℕ} (ρ : Fin n → Fin m)
    (p : Formula S n) (env : Fin m → M.World) (w : M.World) :
    (p.rename ρ).Holds M env w ↔ p.Holds M (env ∘ ρ) w :=
  Silmaril.Proofs.Logic.HybridPolyadic.holds_rename M ρ p env w

theorem holds_map {S T : Signature} (f : S ⟶ T) (M : Model T) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.World) (w : M.World) :
    (p.map f).Holds M env w ↔ p.Holds ((reduct f).obj M) env w :=
  Silmaril.Proofs.Logic.HybridPolyadic.holds_map f M p env w

/-- Hybrid truth is invariant under actual injective bounded model morphisms. -/
theorem holds_hom {S : Signature} {M N : Model S} (h : M ⟶ N) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.World) (w : M.World) :
    p.Holds M env w ↔ p.Holds N (h.map ∘ env) (h.map w) :=
  Silmaril.Proofs.Logic.HybridPolyadic.holds_hom h p env w

@[simp] theorem holds_neg {S : Signature} (M : Model S) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.World) (w : M.World) :
    p.neg.Holds M env w ↔ ¬ p.Holds M env w := Iff.rfl

theorem holds_conj {S : Signature} (M : Model S) {n : ℕ}
    (p q : Formula S n) (env : Fin n → M.World) (w : M.World) :
    (p.conj q).Holds M env w ↔ p.Holds M env w ∧ q.Holds M env w := by
  classical
  change ¬ (p.Holds M env w → ¬ q.Holds M env w) ↔ _
  simp only [not_imp, not_not]

end Formula

theorem sat_hom {S : Signature} {M N : Model S} (h : M ⟶ N) (p : Formula S 0) :
    Sat M p ↔ Sat N p := by
  unfold Sat
  rw [p.holds_hom h, h.point]
  have henv : (h.map ∘ Fin.elim0 : Fin 0 → N.World) = Fin.elim0 := funext (fun i => Fin.elim0 i)
  rw [henv]

/-- The institution uses arbitrary signatures and closed scoped sentences. -/
def institution : Signature ⥤ Room where
  obj S := ⟨Formula S 0, Cat.of (Model S), Sat⟩
  map f := ⟨Formula.map f, reduct f, fun M p => p.holds_map f M Fin.elim0 M.point⟩
  map_id _ := Room.hom_ext (funext Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Formula.map_comp f g)) rfl

def inst : Inst := ⟨Signature, institution⟩

end Silmaril.Logic.HybridPolyadic
