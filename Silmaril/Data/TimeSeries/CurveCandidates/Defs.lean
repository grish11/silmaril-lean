module

public import Silmaril.Data.TimeSeries.Curves.Defs
public import Silmaril.Data.TimeSeries.Defs

/-! Evaluate the candidate tests on the parametrized curve types of `TimeSeries.Curves`. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries

variable {n : Nat} {Time Value Ideal : Type*}

/-- Pull candidate membership back along a real-domain evaluation map, with optional
eligibility depending on the observations and the curve. -/
def curveCandidates {Curve : Type*} (eval : Curve → ℝ → Ideal)
    (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → Curve → Prop := fun _ _ => True) : Set Curve :=
  {c | eligible s c ∧ eval c ∈ candidates model s validTimes budget}

/-- Candidates among continuous curves on the real line. -/
def continuousCandidates [TopologicalSpace Ideal] (model : ErrorModel ℝ Ideal Time Value)
    (s : Series n Time Value) (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → Curves.OpenContinuous Ideal → Prop := fun _ _ => True) :
    Set (Curves.OpenContinuous Ideal) :=
  curveCandidates (fun c => c) model s validTimes budget eligible

section Window

variable {a b : ℝ}

/-- Window candidates require every latent time to lie in the closed interval. The
extension supplies a total function for the base API, while the time loss still uses the
original recorded timestamp. -/
noncomputable def windowCurveCandidates {Curve : Type*} (nonempty : a ≤ b)
    (eval : Curve → Set.Icc a b → Ideal) (model : ErrorModel ℝ Ideal Time Value)
    (s : Series n Time Value) (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → Curve → Prop := fun _ _ => True) : Set Curve :=
  curveCandidates (fun c => Curves.Window.extend nonempty (eval c)) model s
    (fun times => validTimes times ∧ ∀ i, times i ∈ Set.Icc a b) budget eligible

/-- Candidates among continuous curves on `[a,b]`. Singleton intervals are allowed. -/
noncomputable def windowContinuousCandidates [TopologicalSpace Ideal] (nonempty : a ≤ b)
    (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → Curves.WindowContinuous a b Ideal → Prop := fun _ _ => True) :
    Set (Curves.WindowContinuous a b Ideal) :=
  windowCurveCandidates nonempty (fun c => c) model s validTimes budget eligible

end Window

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace Ideal] [ChartedSpace H Ideal]

/-- Candidates among smooth real-domain curves into the manifold model `I`. -/
def smoothCandidates (I : ModelWithCorners ℝ E H) (model : ErrorModel ℝ Ideal Time Value)
    (s : Series n Time Value) (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → Curves.OpenSmooth I Ideal → Prop := fun _ _ => True) :
    Set (Curves.OpenSmooth I Ideal) :=
  curveCandidates (fun c => c) model s validTimes budget eligible

/-- Candidates among smooth curves on a positive-length closed interval, with smoothness
at the boundary supplied by the interval manifold. -/
noncomputable def windowSmoothCandidates {a b : ℝ} [h : Fact (a < b)] (I : ModelWithCorners ℝ E H)
    (model : ErrorModel ℝ Ideal Time Value) (s : Series n Time Value)
    (validTimes : (Fin n → ℝ) → Prop) (budget : Error)
    (eligible : Series n Time Value → Curves.WindowSmooth I a b Ideal → Prop := fun _ _ => True) :
    Set (Curves.WindowSmooth I a b Ideal) :=
  windowCurveCandidates h.out.le (fun c => c) model s validTimes budget eligible

end Silmaril.Data.TimeSeries
