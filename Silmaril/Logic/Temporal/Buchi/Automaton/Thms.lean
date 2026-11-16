module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Defs
public import Silmaril.Logic.Temporal.Buchi.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi.Automaton
variable {Letter NewLetter W : Type} {n : Nat}

theorem accepts_iff_initial (A : Buchi.Automaton Letter n) (word : Word Letter) :
    A.Accepts word ↔ ∃ q ∈ A.initial, A.AcceptsFrom word q := by
  constructor
  · rintro ⟨r, hi, hr, hf⟩
    exact ⟨r 0, hi, r, rfl, hr, hf⟩
  · rintro ⟨q, hi, r, h0, hr, hf⟩
    exact ⟨r, h0.symm ▸ hi, hr, hf⟩

/-- Pairing and projecting actual infinite witnesses gives the product bridge.
The graph path and run are independently defined, rather than product aliases. -/
theorem path_run_iff_product (A : Buchi.Automaton Letter n) (R : W → W → Prop)
    (label : W → Letter) (w : W) (q : Fin n) :
    (∃ p, IsPath R w p ∧ A.AcceptsFrom (label ∘ p) q) ↔
      Buchi.Accepts (A.productStep R label) A.productAccepting (w, q) := by
  constructor
  · rintro ⟨p, ⟨hp0, hp⟩, r, hr0, hr, hf⟩
    refine ⟨fun k => (p k, r k), ?_, fun k => ⟨hp k, hr k⟩, hf⟩
    exact Prod.ext hp0 hr0
  · rintro ⟨s, h0, hs, hf⟩
    refine ⟨fun k => (s k).1, ⟨congrArg Prod.fst h0, fun k => (hs k).1⟩,
      fun k => (s k).2, congrArg Prod.snd h0, fun k => (hs k).2, hf⟩

theorem acceptsPath_iff_product (A : Buchi.Automaton Letter n) (R : W → W → Prop)
    (label : W → Letter) (w : W) :
    A.AcceptsPath R label w ↔
      ∃ q ∈ A.initial, Buchi.Accepts (A.productStep R label) A.productAccepting (w, q) := by
  constructor
  · rintro ⟨p, hp, ha⟩
    obtain ⟨q, hq, hr⟩ := (accepts_iff_initial A _).mp ha
    exact ⟨q, hq, (path_run_iff_product A R label w q).mp ⟨p, hp, hr⟩⟩
  · rintro ⟨q, hq, h⟩
    obtain ⟨p, hp, hr⟩ := (path_run_iff_product A R label w q).mpr h
    exact ⟨p, hp, (accepts_iff_initial A _).mpr ⟨q, hq, hr⟩⟩

/-- Exact nested fixed point on the product, for arbitrary graph branching and
deadlocks. This does not yet eliminate automaton coordinates into base syntax. -/
theorem acceptsPath_iff_gfp (A : Buchi.Automaton Letter n) (R : W → W → Prop)
    (label : W → Letter) (w : W) :
    A.AcceptsPath R label w ↔ ∃ q ∈ A.initial,
      (w, q) ∈ (Buchi.outer (A.productStep R label) A.productAccepting).gfp := by
  rw [acceptsPath_iff_product]
  simp only [Buchi.accepts_iff_gfp]

theorem not_acceptsPath_of_deadlock (A : Buchi.Automaton Letter n)
    (R : W → W → Prop) (label : W → Letter) (w : W) (dead : ∀ v, ¬ R w v) :
    ¬ A.AcceptsPath R label w := by
  rintro ⟨p, ⟨h0, hp⟩, _⟩
  exact dead (p 1) (h0 ▸ hp 0)

theorem accepts_comap (A : Buchi.Automaton Letter n) (f : NewLetter → Letter)
    (word : Word NewLetter) : (A.comap f).Accepts word ↔ A.Accepts (f ∘ word) := Iff.rfl

theorem acceptsPath_comap (A : Buchi.Automaton Letter n) (f : NewLetter → Letter)
    (R : W → W → Prop) (label : W → NewLetter) (w : W) :
    (A.comap f).AcceptsPath R label w ↔ A.AcceptsPath R (f ∘ label) w := Iff.rfl

theorem productStep_comap (A : Buchi.Automaton Letter n) (f : NewLetter → Letter)
    (R : W → W → Prop) (label : W → NewLetter) :
    (A.comap f).productStep R label = A.productStep R (f ∘ label) := rfl

end Silmaril.Logic.Temporal.Buchi.Automaton
