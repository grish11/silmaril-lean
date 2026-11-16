module

public import Silmaril.Proofs.Logic.Temporal.LTL.NNF.Normalization

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF

theorem Formula.dual_dual {Atom : Type} (p : Formula Atom) : p.dual.dual = p := by
  induction p <;> simp_all [dual]

theorem Formula.dual_map {Atom Atom' : Type} (f : Atom → Atom') (p : Formula Atom) :
    (p.map f).dual = p.dual.map f := by
  induction p <;> simp_all [map, dual]

theorem Formula.holds_map {Atom Atom' : Type} (f : Atom → Atom')
    (word : Nat → Atom' → Prop) (p : Formula Atom) (n : Nat) :
    (p.map f).Holds word n ↔ p.Holds (fun t a => word t (f a)) n := by
  induction p generalizing n with
  | pos a => rfl
  | neg a => rfl
  | bot => rfl
  | top => rfl
  | conj p q hp hq => exact and_congr (hp n) (hq n)
  | disj p q hp hq => exact or_congr (hp n) (hq n)
  | next p hp => exact hp (n+1)
  | «until» p q hp hq =>
    exact exists_congr fun d => and_congr (hq (n+d))
      (forall_congr' fun i => imp_congr_right fun _ => hp (n+i))
  | release p q hp hq =>
    exact forall_congr' fun d => or_congr (hq (n+d))
      (exists_congr fun i => and_congr_right fun _ => hp (n+i))

/-- Arbitrary atom maps, including maps that identify distinct input atoms. -/
theorem normalize_map {Atom Atom' : Type} (f : Atom → Atom') (p : LTL.Formula Atom)
    (b : Bool) : normalize b (p.map f) = (normalize b p).map f := by
  induction p generalizing b with
  | atom a => cases b <;> rfl
  | bot => cases b <;> rfl
  | not p hp => cases b <;> simp [normalize, LTL.Formula.map, hp]
  | imp p q hp hq => cases b <;> simp [normalize, LTL.Formula.map, Formula.map, hp, hq]
  | and p q hp hq => cases b <;> simp [normalize, LTL.Formula.map, Formula.map, hp, hq]
  | or p q hp hq => cases b <;> simp [normalize, LTL.Formula.map, Formula.map, hp, hq]
  | next p hp => cases b <;> simp [normalize, LTL.Formula.map, Formula.map, hp]
  | «until» p q hp hq => cases b <;> simp [normalize, LTL.Formula.map, Formula.map, hp, hq]

end Silmaril.Logic.Temporal.LTL.NNF
