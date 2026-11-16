module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Thms

/-! Typed membership rooms only. Raw-source adequacy is a separate obligation;
these statements must not be advertised as a theorem about an unchecked RawPattern.
The target models are precisely source valuations paired with output values,
not arbitrary uninterpreted-predicate models with an unrelated interpretation. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open CategoryTheory Silmaril.Inst Silmaril.Logic.Smt
open Silmaril.Logic.Institution (Room Corridor)

abbrev Point (s : ValueSort) := Valuation × s.Value

abbrev Characteristic (s : ValueSort) :=
  Uflia.Quantified.Formula signature (fun _ : Fin 1 => s.code)

def Pattern.characteristic {s : ValueSort} (p : Pattern s) : Characteristic s := p.compile (.var 0)

def typedSourceRoom (s : ValueSort) : Room :=
  ⟨Pattern s, Disc.cat (Point s), fun point p => point.2 ∈ p.denote point.1⟩

def pairedTargetRoom (s : ValueSort) : Room :=
  ⟨Characteristic s, Disc.cat (Point s), fun point p =>
    Uflia.Quantified.Formula.Holds p (target point.1) (fun _ => point.2)⟩

theorem characteristic_correct {s : ValueSort} (p : Pattern s) (point : Point s) :
    Uflia.Quantified.Formula.Holds p.characteristic (target point.1) (fun _ => point.2) ↔
      point.2 ∈ p.denote point.1 :=
  compile_correct p point.1 (fun _ => point.2) (.var 0)

def typedCorridor (s : ValueSort) : Corridor (typedSourceRoom s) (pairedTargetRoom s) :=
  ⟨Pattern.characteristic, 𝟭 _, fun point p => characteristic_correct p point⟩

theorem typed_modelExpansive (s : ValueSort) : (typedCorridor s).ModelExpansive :=
  fun point => ⟨point, rfl⟩

theorem theory_models_iff {s : ValueSort} (H : Set (Pattern s)) (point : Point s) :
    (∀ p ∈ H, point.2 ∈ p.denote point.1) ↔
      (∀ q ∈ Pattern.characteristic '' H,
        Uflia.Quantified.Formula.Holds q (target point.1) (fun _ => point.2)) := by
  constructor
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact (characteristic_correct p point).mpr (h p hp)
  · intro h p hp
    exact (characteristic_correct p point).mp (h p.characteristic ⟨p, hp, rfl⟩)

theorem theory_sat_iff {s : ValueSort} (H : Set (Pattern s)) :
    (∃ point : Point s, ∀ p ∈ H, point.2 ∈ p.denote point.1) ↔
      (∃ point : Point s, ∀ q ∈ Pattern.characteristic '' H,
        Uflia.Quantified.Formula.Holds q (target point.1) (fun _ => point.2)) :=
  exists_congr (theory_models_iff H)

theorem theory_unsat_iff {s : ValueSort} (H : Set (Pattern s)) :
    (¬ ∃ point : Point s, ∀ p ∈ H, point.2 ∈ p.denote point.1) ↔
      (¬ ∃ point : Point s, ∀ q ∈ Pattern.characteristic '' H,
        Uflia.Quantified.Formula.Holds q (target point.1) (fun _ => point.2)) :=
  not_congr (theory_sat_iff H)

theorem theory_entails_iff {s : ValueSort} (H : Set (Pattern s)) (p : Pattern s) :
    (typedSourceRoom s).Entails H p ↔
      (pairedTargetRoom s).Entails (Pattern.characteristic '' H) p.characteristic :=
  (typedCorridor s).entails_map_iff (typed_modelExpansive s) H p

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
