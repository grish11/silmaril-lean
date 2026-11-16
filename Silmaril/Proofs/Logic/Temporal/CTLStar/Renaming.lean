module

public import Silmaril.Logic.Temporal.CTLStar.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar
open CategoryTheory Silmaril.Logic.Institution

mutual
theorem StateFormula.map_id {S : Signature} (p : StateFormula S) : p.map (𝟙 S) = p := by
  cases p with
  | atom => rfl
  | bot => rfl
  | neg p => exact congrArg StateFormula.neg p.map_id
  | conj p q => exact congrArg₂ StateFormula.conj p.map_id q.map_id
  | existsPath p => exact congrArg StateFormula.existsPath p.map_id

theorem PathFormula.map_id {S : Signature} (p : PathFormula S) : p.map (𝟙 S) = p := by
  cases p with
  | state p => exact congrArg PathFormula.state p.map_id
  | neg p => exact congrArg PathFormula.neg p.map_id
  | conj p q => exact congrArg₂ PathFormula.conj p.map_id q.map_id
  | next p => exact congrArg PathFormula.next p.map_id
  | «until» p q => exact congrArg₂ PathFormula.until p.map_id q.map_id
end

mutual
theorem StateFormula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (p : StateFormula S) : p.map (f ≫ g) = (p.map f).map g := by
  cases p with
  | atom => rfl
  | bot => rfl
  | neg p => exact congrArg StateFormula.neg (p.map_comp f g)
  | conj p q => exact congrArg₂ StateFormula.conj (p.map_comp f g) (q.map_comp f g)
  | existsPath p => exact congrArg StateFormula.existsPath (p.map_comp f g)

theorem PathFormula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (p : PathFormula S) : p.map (f ≫ g) = (p.map f).map g := by
  cases p with
  | state p => exact congrArg PathFormula.state (p.map_comp f g)
  | neg p => exact congrArg PathFormula.neg (p.map_comp f g)
  | conj p q => exact congrArg₂ PathFormula.conj (p.map_comp f g) (q.map_comp f g)
  | next p => exact congrArg PathFormula.next (p.map_comp f g)
  | «until» p q => exact congrArg₂ PathFormula.until (p.map_comp f g) (q.map_comp f g)
end

mutual
theorem StateFormula.holds_map {S T : Signature} (f : S ⟶ T) (M : Model T)
    (p : StateFormula S) (w : M.toModal.World) :
    (p.map f).Holds M w ↔ p.Holds (CTL.reduct f M) w := by
  cases p with
  | atom => rfl
  | bot => rfl
  | neg p => exact not_congr (p.holds_map f M w)
  | conj p q => exact and_congr (p.holds_map f M w) (q.holds_map f M w)
  | existsPath p =>
    exact exists_congr fun path => and_congr Iff.rfl (p.holds_map f M path 0)

theorem PathFormula.holds_map {S T : Signature} (f : S ⟶ T) (M : Model T)
    (p : PathFormula S) (path : Path M.toModal.accessible) (i : Nat) :
    (p.map f).Holds M path i ↔ p.Holds (CTL.reduct f M) path i := by
  cases p with
  | state p => exact p.holds_map f M (path.state i)
  | neg p => exact not_congr (p.holds_map f M path i)
  | conj p q => exact and_congr (p.holds_map f M path i) (q.holds_map f M path i)
  | next p => exact and_congr Iff.rfl (p.holds_map f M path (i+1))
  | «until» p q =>
    exact exists_congr fun d => and_congr Iff.rfl
      (and_congr (q.holds_map f M path (i+d))
        (forall_congr' fun j => imp_congr_right fun _ => p.holds_map f M path (i+j)))
end

end Silmaril.Logic.Temporal.CTLStar
