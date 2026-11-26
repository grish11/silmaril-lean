module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.UnitInterval

/-!
# Real-time curves

The open time domain is the whole real line. The closed time domain is the
subtype `[0,1]`, with general windows `[a,b]` also available. Smooth windows
use Mathlib's manifold structure for `a < b`. At the endpoints smoothness is
tested within `[a,b]`, so the clamped extension is smooth on the window.
The value space can have any real model with corners.

A reparametrization class retains a curve up to the chosen time bijections.
The endpoints descend for oriented windows. More generally, `CurveClass.eval`
takes a time fixed by every allowed bijection. The trace is the set of values
attained and discards the order and fibers of the parametrization.
-/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Curves

open Set
open scoped ContDiff Manifold

noncomputable section

variable {T M : Type*} [TopologicalSpace M]
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

/-- Mathlib's closed real interval manifold requires a fact about its endpoints. -/
scoped instance unitIntervalFact : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

/-- Continuous curves on the whole real line. -/
abbrev OpenContinuous (M : Type*) [TopologicalSpace M] := C(ℝ, M)

/-- Continuous curves on the closed interval `[a,b]`. -/
abbrev WindowContinuous (a b : ℝ) (M : Type*) [TopologicalSpace M] := C(Icc a b, M)

/-- Continuous curves on `[0,1]`. -/
abbrev ClosedContinuous (M : Type*) [TopologicalSpace M] := WindowContinuous 0 1 M

/-- Smooth curves on the whole real line with target model `I`. -/
abbrev OpenSmooth (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := C^∞⟮𝓘(ℝ), ℝ; I, M⟯

/-- Smooth curves on `[a,b]`, including both boundary points, with target model `I`. -/
abbrev WindowSmooth (I : ModelWithCorners ℝ E H) (a b : ℝ) [Fact (a < b)]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] := C^∞⟮𝓡∂ 1, Icc a b; I, M⟯

/-- Smooth curves on `[0,1]` with target model `I`. -/
abbrev ClosedSmooth (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := WindowSmooth I 0 1 M

namespace Window

variable {a b : ℝ}

/-- The first time in a nonempty closed window. -/
def start (h : a ≤ b) : Icc a b := ⟨a, le_rfl, h⟩

/-- The last time in a nonempty closed window. -/
def finish (h : a ≤ b) : Icc a b := ⟨b, h, le_rfl⟩

/-- Restrict an ambient function continuous within a window to the interval subtype. -/
def ofContinuousOn (f : ℝ → M) (hf : ContinuousOn f (Icc a b)) : WindowContinuous a b M :=
  ⟨fun t => f t, continuousOn_iff_continuous_domRestrict.mp hf⟩

/-- Regard an interval map as an ambient function by clamping time to the window. -/
def extend (h : a ≤ b) (f : Icc a b → M) : ℝ → M := f ∘ Set.projIcc a b h

/-- Restrict an ambient function smooth within a window to the interval manifold. -/
def ofContMDiffOn [Fact (a < b)] (f : ℝ → M)
    (hf : ContMDiffOn 𝓘(ℝ) I ∞ f (Icc a b)) : WindowSmooth I a b M :=
  ⟨fun t => f t, (hf.comp_contMDiff contMDiff_subtypeVal_Icc) fun t => t.2⟩

end Window

/-- Restrict an ambient function continuous on the unit interval. -/
def ClosedContinuous.ofContinuousOn (f : ℝ → M) (hf : ContinuousOn f unitInterval) :
    ClosedContinuous M :=
  Window.ofContinuousOn f hf

/-- Restrict an ambient function smooth on the unit interval, including its endpoints. -/
def ClosedSmooth.ofContMDiffOn (f : ℝ → M) (hf : ContMDiffOn 𝓘(ℝ) I ∞ f unitInterval) :
    ClosedSmooth I M :=
  Window.ofContMDiffOn f hf

/-- Observe an open continuous curve on a finite window at its original times. -/
def OpenContinuous.window (c : OpenContinuous M) (a b : ℝ) : WindowContinuous a b M :=
  Window.ofContinuousOn c c.continuous.continuousOn

/-- Observe an open smooth curve on a positive-length finite window at its original times. -/
def OpenSmooth.window (c : OpenSmooth I M) (a b : ℝ) [Fact (a < b)] : WindowSmooth I a b M :=
  Window.ofContMDiffOn c c.contMDiff.contMDiffOn

namespace Reparam

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [TopologicalSpace T] [ChartedSpace K T]

/-- All smooth time bijections with smooth inverse. Orientation reversal is allowed. -/
def diffeomorphisms (J : ModelWithCorners ℝ F K) : Subgroup (Equiv.Perm T) where
  carrier := {e | ContMDiff J J ∞ e ∧ ContMDiff J J ∞ e.symm}
  one_mem' := ⟨contMDiff_id, contMDiff_id⟩
  mul_mem' := fun ⟨hf, hf'⟩ ⟨hg, hg'⟩ => ⟨hf.comp hg, hg'.comp hf'⟩
  inv_mem' := fun ⟨hf, hf'⟩ => ⟨hf', hf⟩

/-- The strictly increasing smooth time bijections with smooth inverse. -/
def increasing (J : ModelWithCorners ℝ F K) [LinearOrder T] : Subgroup (Equiv.Perm T) where
  carrier := {e | e ∈ diffeomorphisms J ∧ StrictMono e}
  one_mem' := ⟨(diffeomorphisms J).one_mem, strictMono_id⟩
  mul_mem' := fun ⟨hf, hmono⟩ ⟨hg, hmono'⟩ => ⟨(diffeomorphisms J).mul_mem hf hg,
    hmono.comp hmono'⟩
  inv_mem' := by
    rintro e ⟨he, hmono⟩
    exact ⟨(diffeomorphisms J).inv_mem he, fun _ _ h => hmono.lt_iff_lt.mp (by simpa using h)⟩

/-- Use the forward map of a smooth time bijection for time precomposition. -/
def smoothMap (J : ModelWithCorners ℝ F K) (e : Equiv.Perm T)
    (he : e ∈ diffeomorphisms J) : C^∞⟮J, T; J, T⟯ :=
  ⟨e, he.1⟩

/-- Orientation-preserving smooth reparametrizations of the real line. -/
abbrev openIncreasing : Subgroup (Equiv.Perm ℝ) := increasing 𝓘(ℝ)

/-- Orientation-preserving smooth reparametrizations of a positive-length window. -/
abbrev windowIncreasing (a b : ℝ) [Fact (a < b)] : Subgroup (Equiv.Perm (Icc a b)) :=
  increasing (𝓡∂ 1)

/-- Orientation-preserving smooth reparametrizations of `[0,1]`. -/
abbrev closedIncreasing : Subgroup (Equiv.Perm unitInterval) := windowIncreasing 0 1

variable {a b : ℝ} [h : Fact (a < b)]

/-- Forget the orientation condition on a smooth clock. -/
theorem increasing_le_diffeomorphisms (J : ModelWithCorners ℝ F K) [LinearOrder T] :
    increasing (T := T) J ≤ diffeomorphisms J := fun _ he => he.1

/-- Increasing smooth clocks fix the left endpoint. -/
theorem fixes_start {e : Equiv.Perm (Icc a b)} (he : e ∈ windowIncreasing a b) :
    e (Window.start h.out.le) = Window.start h.out.le := by
  let t := Window.start h.out.le
  have ht : t ≤ e.symm t := (e.symm t).2.1
  exact le_antisymm (by simpa only [Equiv.apply_symm_apply] using he.2.monotone ht) (e t).2.1

/-- Increasing smooth clocks fix the right endpoint. -/
theorem fixes_finish {e : Equiv.Perm (Icc a b)} (he : e ∈ windowIncreasing a b) :
    e (Window.finish h.out.le) = Window.finish h.out.le := by
  let t := Window.finish h.out.le
  have ht : e.symm t ≤ t := (e.symm t).2.2
  exact le_antisymm (e t).2.2 (by simpa only [Equiv.apply_symm_apply] using he.2.monotone ht)

end Reparam

variable {X A : Type*}

/-- Two representatives are equivalent if the second is the first precomposed with a
permitted time bijection. The function `view` reads the parametrized function from a
representative, for example from a bundled continuous or smooth map. -/
def reparamSetoid (G : Subgroup (Equiv.Perm T)) (view : A → T → X) : Setoid A where
  r f g := ∃ e ∈ G, ∀ t, view g t = view f (e t)
  iseqv := ⟨fun _ => ⟨1, G.one_mem, fun _ => rfl⟩,
    fun ⟨e, he, h⟩ => ⟨e⁻¹, G.inv_mem he, fun t => by simpa using (h (e.symm t)).symm⟩,
    fun ⟨e, he, h⟩ ⟨d, hd, k⟩ => ⟨e * d, G.mul_mem he hd, fun t => (k t).trans (h (d t))⟩⟩

/-- Curves modulo the time bijections in `G`. -/
abbrev CurveClass (G : Subgroup (Equiv.Perm T)) (view : A → T → X) :=
  Quotient (reparamSetoid G view)

/-- Maps into a plain type modulo *arbitrary* bijections of time. No topology is required.
The class can distinguish functions with the same range, for example an injective
function and a noninjective function. -/
abbrev Unparametrized (T X : Type*) :=
  CurveClass (⊤ : Subgroup (Equiv.Perm T)) (fun f : T → X => f)

namespace CurveClass

variable {G G' : Subgroup (Equiv.Perm T)} {view : A → T → X}

/-- Take the class of a parametrized representative. -/
def mk (G : Subgroup (Equiv.Perm T)) (view : A → T → X) (f : A) : CurveClass G view :=
  Quotient.mk _ f

/-- Descend a map of representatives that postcomposes their values by `k`.
The allowed time group may stay the same or be enlarged. -/
def map {B Y : Type*} {view' : B → T → Y} (hG : G ≤ G') (F : A → B) (k : X → Y)
    (hF : ∀ f t, view' (F f) t = k (view f t)) : CurveClass G view → CurveClass G' view' :=
  Quotient.map F fun _ _ h => by
    obtain ⟨e, he, h⟩ := h
    exact ⟨e, hG he, fun t => (hF _ _).trans ((congrArg k (h t)).trans (hF _ _).symm)⟩

/-- Discard orientation restrictions or otherwise enlarge the allowed time group. -/
def weaken (hG : G ≤ G') : CurveClass G view → CurveClass G' view :=
  map hG id id fun _ _ => rfl

/-- Forget regularity and allow all time bijections. -/
def toUnparametrized : CurveClass G view → Unparametrized T X :=
  map le_top view id fun _ _ => rfl

/-- Set of values attained by a representative. Every permitted clock is surjective. -/
def trace : CurveClass G view → Set X :=
  Quotient.lift (fun f => Set.range (view f)) fun f g h => by
    obtain ⟨e, _, h⟩ := h
    rw [show view g = view f ∘ e from funext h, e.surjective.range_comp]

/-- Evaluation descends at a time that every permitted bijection fixes. -/
def eval (t : T) (fixed : ∀ e ∈ G, e t = t) : CurveClass G view → X :=
  Quotient.lift (fun f => view f t) fun _ _ h => by
    obtain ⟨e, he, h⟩ := h
    simpa only [fixed e he] using (h t).symm

section Window

variable {a b : ℝ} [h : Fact (a < b)] {read : A → Icc a b → X}

/-- First value of an oriented window curve. Increasing clocks fix the first time. -/
def start : CurveClass (Reparam.windowIncreasing a b) read → X :=
  eval (Window.start h.out.le) fun _ he => Reparam.fixes_start he

/-- Last value of an oriented window curve. Increasing clocks fix the last time. -/
def finish : CurveClass (Reparam.windowIncreasing a b) read → X :=
  eval (Window.finish h.out.le) fun _ he => Reparam.fixes_finish he

end Window

end CurveClass

namespace Unparametrized

/-- Take the class of a plain function of time. -/
def mk (f : T → X) : Unparametrized T X :=
  CurveClass.mk ⊤ id f

variable {Y : Type*}

/-- Postcompose a plain unparametrized curve by any function of its values. -/
def postcomp (k : X → Y) : Unparametrized T X → Unparametrized T Y :=
  CurveClass.map le_rfl (fun f => k ∘ f) k fun _ _ => rfl

end Unparametrized

section Bundled

variable [TopologicalSpace T]
variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [ChartedSpace K T] {J : ModelWithCorners ℝ F K}

/-- Classes of continuous representatives under the specified group of time bijections. -/
abbrev ContinuousClass (G : Subgroup (Equiv.Perm T)) (M : Type*) [TopologicalSpace M] :=
  CurveClass G (fun c : C(T, M) => (c : T → M))

/-- Take the class of a bundled continuous curve under the chosen clock group. -/
def ContinuousClass.mk (G : Subgroup (Equiv.Perm T)) (c : C(T, M)) : ContinuousClass G M :=
  CurveClass.mk G _ c

/-- Classes of smooth representatives under the specified group of time bijections. -/
abbrev SmoothClass (G : Subgroup (Equiv.Perm T)) (J : ModelWithCorners ℝ F K)
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  CurveClass G (fun c : C^∞⟮J, T; I, M⟯ => (c : T → M))

/-- Take the class of a bundled smooth curve under the chosen clock group. -/
def SmoothClass.mk (G : Subgroup (Equiv.Perm T)) (c : C^∞⟮J, T; I, M⟯) :
    SmoothClass G J I M :=
  CurveClass.mk G _ c

/-- Open smooth curves modulo increasing smooth clocks. -/
abbrev OrientedOpenSmooth (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := SmoothClass Reparam.openIncreasing 𝓘(ℝ) I M

/-- Smooth window curves modulo increasing smooth clocks. -/
abbrev OrientedWindowSmooth (I : ModelWithCorners ℝ E H) (a b : ℝ) [Fact (a < b)]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  SmoothClass (Reparam.windowIncreasing a b) (𝓡∂ 1) I M

/-- Closed smooth curves modulo increasing smooth clocks. -/
abbrev OrientedClosedSmooth (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] := SmoothClass Reparam.closedIncreasing (𝓡∂ 1) I M

/-- Forget the choice of increasing clock for an open smooth curve. -/
def OpenSmooth.toOriented (c : OpenSmooth I M) : OrientedOpenSmooth I M :=
  SmoothClass.mk _ c

/-- Forget the choice of increasing clock for a smooth window curve. -/
def WindowSmooth.toOriented {a b : ℝ} [Fact (a < b)] (c : WindowSmooth I a b M) :
    OrientedWindowSmooth I a b M :=
  SmoothClass.mk _ c

/-- Forget the choice of increasing clock for a closed smooth curve. -/
def ClosedSmooth.toOriented (c : ClosedSmooth I M) : OrientedClosedSmooth I M :=
  SmoothClass.mk Reparam.closedIncreasing c

variable {G : Subgroup (Equiv.Perm T)} {N : Type*} [TopologicalSpace N]

/-- Continuous value postcomposition on classes of continuous curves. -/
def ContinuousClass.postcomp (k : C(M, N)) : ContinuousClass G M → ContinuousClass G N :=
  CurveClass.map le_rfl (fun c => k.comp c) k fun _ _ => rfl

/-- Forget the smoothness of the representatives while keeping the same clock relation. -/
def SmoothClass.toContinuous : SmoothClass G J I M → ContinuousClass G M :=
  CurveClass.map le_rfl (fun c => (c : C(T, M))) id fun _ _ => rfl

/-- Forget the increasing condition while still requiring smooth clocks and smooth inverses. -/
def SmoothClass.forgetOrientation [LinearOrder T] :
    SmoothClass (Reparam.increasing (T := T) J) J I M →
      SmoothClass (Reparam.diffeomorphisms (T := T) J) J I M :=
  CurveClass.weaken (Reparam.increasing_le_diffeomorphisms (T := T) J)

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [ChartedSpace H' N] {I' : ModelWithCorners ℝ E' H'}

/-- Smooth value postcomposition on classes of smooth curves. -/
def SmoothClass.postcomp (k : C^∞⟮I, M; I', N⟯) : SmoothClass G J I M → SmoothClass G J I' N :=
  CurveClass.map le_rfl (fun c => k.comp c) k fun _ _ => rfl

end Bundled

end

end Silmaril.Data.TimeSeries.Curves
