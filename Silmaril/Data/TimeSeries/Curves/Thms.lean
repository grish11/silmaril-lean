module

public import Silmaril.Data.TimeSeries.Curves.Defs
import Silmaril.Proofs.Data.TimeSeries.Curves.Window

/-!
# Laws for real-time curves

Use Mathlib's `ContinuousMap.comp` and `ContMDiffMap.comp` to precompose
parametrized curves in time or postcompose them in values. Precomposition by a
permitted bijection leaves the class unchanged. A general time map, such as a
restriction to a finite window, acts on the parametrized representative.
Smooth and continuous value maps induce postcomposition on their respective
curve classes. Any value function induces postcomposition after passing to
the quotient of plain time-to-value maps by time bijections. The trace is the
point set of attained values. Distinct unparametrized classes may have the same
trace.
-/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Curves

open Set
open scoped ContDiff Manifold

variable {T X Y A B : Type*}

namespace Window

variable {M : Type*} {a b : ℝ}

@[simp] theorem coe_start (h : a ≤ b) : (start h : ℝ) = a := rfl

@[simp] theorem coe_finish (h : a ≤ b) : (finish h : ℝ) = b := rfl

@[simp] theorem extend_apply (h : a ≤ b) (f : Icc a b → M) (t : Icc a b) :
    extend h f t = f t := by simp [extend]

variable [TopologicalSpace M]

theorem continuousOn_iff (f : ℝ → M) :
    ContinuousOn f (Icc a b) ↔ Continuous (fun t : Icc a b => f t) :=
  continuousOn_iff_continuous_domRestrict

@[simp] theorem ofContinuousOn_apply (f : ℝ → M) (hf : ContinuousOn f (Icc a b))
    (t : Icc a b) : ofContinuousOn f hf t = f t := rfl

theorem continuous_extend (h : a ≤ b) (f : WindowContinuous a b M) : Continuous (extend h f) :=
  f.continuous.comp continuous_projIcc

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [h : Fact (a < b)]

/-- Smoothness on the interval is exactly manifold smoothness of the subtype map.
This tests the two endpoints within `[a,b]`. -/
theorem contMDiffOn_iff (f : ℝ → M) :
    ContMDiffOn 𝓘(ℝ) I ∞ f (Icc a b) ↔
      ContMDiff (𝓡∂ 1) I ∞ (fun t : Icc a b => f t) :=
  Proofs.Data.TimeSeries.Curves.Window.contMDiffOn_iff f

@[simp] theorem ofContMDiffOn_apply (f : ℝ → M) (hf : ContMDiffOn 𝓘(ℝ) I ∞ f (Icc a b))
    (t : Icc a b) : ofContMDiffOn f hf t = f t := rfl

theorem contMDiffOn_extend (f : WindowSmooth I a b M) :
    ContMDiffOn 𝓘(ℝ) I ∞ (extend h.out.le f) (Icc a b) :=
  contMDiffOn_comp_projIcc_iff.mpr f.contMDiff

end Window

namespace CurveClass

variable {G G' : Subgroup (Equiv.Perm T)} {view : A → T → X} {view' : B → T → Y}

/-- Equality of classes is witnessed by a single permitted time bijection. -/
theorem mk_eq_mk_iff {f g : A} :
    mk G view f = mk G view g ↔ ∃ e ∈ G, ∀ t, view g t = view f (e t) :=
  ⟨Quotient.exact, Quotient.sound (s := reparamSetoid G view)⟩

/-- Precomposing a representative by an allowed time bijection preserves its class. -/
theorem mk_precomp {e : Equiv.Perm T} (he : e ∈ G) {f g : A}
    (hg : ∀ t, view g t = view f (e t)) : mk G view g = mk G view f :=
  (mk_eq_mk_iff.mpr ⟨e, he, hg⟩).symm

@[simp] theorem map_mk (hG : G ≤ G') (F : A → B) (k : X → Y)
    (hF : ∀ f t, view' (F f) t = k (view f t)) (f : A) :
    map hG F k hF (mk G view f) = mk G' view' (F f) := rfl

@[simp] theorem trace_mk (f : A) : trace (mk G view f) = Set.range (view f) := rfl

@[simp] theorem trace_toUnparametrized (q : CurveClass G view) :
    q.toUnparametrized.trace = q.trace := by
  induction q using Quotient.ind
  rfl

@[simp] theorem trace_weaken (hG : G ≤ G') (q : CurveClass G view) :
    (q.weaken hG).trace = q.trace := by
  induction q using Quotient.ind
  rfl

theorem trace_map (hG : G ≤ G') (F : A → B) (k : X → Y)
    (hF : ∀ f t, view' (F f) t = k (view f t)) (q : CurveClass G view) :
    (map hG F k hF q).trace = k '' q.trace := by
  induction q using Quotient.ind with | _ f =>
    change Set.range (view' (F f)) = k '' Set.range (view f)
    rw [show view' (F f) = k ∘ view f from funext (hF f), Set.range_comp]

/-- Value postcomposition commutes with passing to the quotient of plain
time-to-value maps by time bijections. Taking `k = id` gives the corresponding
law for forgetful maps. -/
theorem toUnparametrized_map (hG : G ≤ G') (F : A → B) (k : X → Y)
    (hF : ∀ f t, view' (F f) t = k (view f t)) (q : CurveClass G view) :
    (map hG F k hF q).toUnparametrized = Unparametrized.postcomp k q.toUnparametrized := by
  induction q using Quotient.ind with | _ f =>
    exact mk_eq_mk_iff.mpr ⟨1, Subgroup.mem_top _, fun t => (hF f t).symm⟩

variable {a b : ℝ} [h : Fact (a < b)] {read : A → Icc a b → X}

@[simp] theorem start_mk (f : A) :
    start (mk (Reparam.windowIncreasing a b) read f) = read f (Window.start h.out.le) := rfl

@[simp] theorem finish_mk (f : A) :
    finish (mk (Reparam.windowIncreasing a b) read f) = read f (Window.finish h.out.le) := rfl

end CurveClass

namespace Unparametrized

/-- Any time bijection may witness equality of unparametrized classes. -/
theorem mk_eq_mk_iff {f g : T → X} :
    mk f = mk g ↔
      ∃ e : Equiv.Perm T, ∀ t, g t = f (e t) := by
  simp [mk, CurveClass.mk_eq_mk_iff]

@[simp] theorem postcomp_mk (k : X → Y) (f : T → X) :
    postcomp k (mk f) = mk (k ∘ f) := rfl

theorem trace_postcomp (k : X → Y) (q : Unparametrized T X) :
    (postcomp k q).trace = k '' q.trace :=
  CurveClass.trace_map le_rfl (fun f => k ∘ f) k (fun _ _ => rfl) q

@[simp] theorem postcomp_id (q : Unparametrized T X) : postcomp id q = q := by
  induction q using Quotient.ind
  rfl

theorem postcomp_comp {Z : Type*} (k : X → Y) (l : Y → Z) (q : Unparametrized T X) :
    postcomp l (postcomp k q) = postcomp (l ∘ k) q := by
  induction q using Quotient.ind
  rfl

end Unparametrized

section Bundled

variable {M : Type*} [TopologicalSpace M]
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

@[simp] theorem OpenContinuous.window_apply (c : OpenContinuous M) {a b : ℝ} (t : Icc a b) :
    c.window a b t = c t := rfl

@[simp] theorem OpenSmooth.window_apply (c : OpenSmooth I M) {a b : ℝ} [Fact (a < b)]
    (t : Icc a b) : c.window a b t = c t := rfl

@[simp] theorem OpenSmooth.window_toContinuous (c : OpenSmooth I M) (a b : ℝ) [Fact (a < b)] :
    (c.window a b : WindowContinuous a b M) = OpenContinuous.window (c : OpenContinuous M) a b := rfl

variable [TopologicalSpace T]
variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [ChartedSpace K T] {J : ModelWithCorners ℝ F K}
variable {G : Subgroup (Equiv.Perm T)}

@[simp] theorem Reparam.smoothMap_apply (e : Equiv.Perm T) (he : e ∈ Reparam.diffeomorphisms J)
    (t : T) : Reparam.smoothMap J e he t = e t := rfl

/-- Composing the values of a curve commutes with precomposing its time map. -/
theorem smooth_postcomp_precomp {N E' H' : Type*} [TopologicalSpace N] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] [ChartedSpace H' N]
    {I' : ModelWithCorners ℝ E' H'} (k : C^∞⟮I, M; I', N⟯) (c : C^∞⟮J, T; I, M⟯)
    (e : C^∞⟮J, T; J, T⟯) : (k.comp c).comp e = k.comp (c.comp e) := rfl

/-- Successive time changes compose as permutations of time. -/
theorem smooth_precomp_mul (c : C^∞⟮J, T; I, M⟯) {e d : Equiv.Perm T}
    (he : e ∈ Reparam.diffeomorphisms J) (hd : d ∈ Reparam.diffeomorphisms J) :
    (c.comp (Reparam.smoothMap J e he)).comp (Reparam.smoothMap J d hd) =
      c.comp (Reparam.smoothMap J (e * d) ((Reparam.diffeomorphisms J).mul_mem he hd)) := rfl

/-- The class of a smooth curve absorbs permitted smooth changes of time. -/
theorem SmoothClass.mk_precomp (hG : G ≤ Reparam.diffeomorphisms J)
    (c : C^∞⟮J, T; I, M⟯) {e : Equiv.Perm T} (he : e ∈ G) :
    mk G (c.comp (Reparam.smoothMap J e (hG he))) = mk G c :=
  CurveClass.mk_precomp he fun _ => rfl

@[simp] theorem SmoothClass.toUnparametrized_toContinuous (q : SmoothClass G J I M) :
    q.toContinuous.toUnparametrized = q.toUnparametrized := by
  induction q using Quotient.ind
  rfl

/-- The forgetful maps on value regularity and time orientation commute. -/
theorem SmoothClass.toContinuous_forgetOrientation [LinearOrder T]
    (q : SmoothClass (Reparam.increasing (T := T) J) J I M) :
    q.forgetOrientation.toContinuous =
      q.toContinuous.weaken (Reparam.increasing_le_diffeomorphisms (T := T) J) := by
  induction q using Quotient.ind
  rfl

variable {N E' H' : Type*} [TopologicalSpace N] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [ChartedSpace H' N] {I' : ModelWithCorners ℝ E' H'}

/-- Forgetting smoothness commutes with smooth value postcomposition. -/
theorem SmoothClass.toContinuous_postcomp (k : C^∞⟮I, M; I', N⟯) (q : SmoothClass G J I M) :
    (SmoothClass.postcomp k q).toContinuous = ContinuousClass.postcomp k q.toContinuous := by
  induction q using Quotient.ind
  rfl

end Bundled

end Silmaril.Data.TimeSeries.Curves
