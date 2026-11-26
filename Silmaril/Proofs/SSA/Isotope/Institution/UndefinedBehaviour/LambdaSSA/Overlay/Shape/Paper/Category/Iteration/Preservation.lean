module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.ExactSum.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Representatives

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches ContinuationContext)
open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
  (iterationBody iterationDispatch iterationDispatch_valueBranches iterateRegion_valueBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
  (ofType ofRegion iterateSum iterateSum_ofRegion exists_ofRegion)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
  (ValueTyped ReturnsTyped returns_typed)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
  (Arrow interpretSingleton iterationGraph iterateObservations singlePayload tagIterationOutcome)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
  (singletonInterpretation)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category
  (ops literal_outcomes branch_label_outcomes outcomes_of_regionAt lift_outcomes)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (PureValue)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (case_pure_inl case_pure_inr)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B : Ty κ} {r : LambdaSSA.Region Φ}

set_option backward.isDefEq.respectTransparency false

section Captures

variable {Γ : List (Ty κ)}

private theorem dispatch_typed :
    LambdaSSA.Region.LSubst.HasType (A :: Γ) [.coprod B A] [A, B] (fun _ => (iterationDispatch : LambdaSSA.Region Φ)) := by
  intro i T hit
  cases List.mem_singleton.mp (List.mem_of_getElem? hit)
  exact (iterationDispatch_valueBranches A B).hasType

private abbrev step (hr : ValueBranches (A :: Γ) r [.coprod B A]) :
    UB.Typed (Φ := Φ) (A :: Γ) [A, B] :=
  ⟨iterationBody r, hr.hasType.lsubst dispatch_typed⟩

private abbrev dispatcher (A B : Ty κ) : UB.Typed (Φ := Φ) (.coprod B A :: A :: Γ) [A, B] :=
  ⟨iterationDispatch, (iterationDispatch_valueBranches A B).hasType⟩

private theorem dispatch_inl (M : Shape.Model.{u,v,w,x} Φ (A :: Γ)) (b : Value M.raw.α) (s : M.raw.σ) :
    nativeOutcomes (dispatcher (Γ := Γ) A B) (extendModel M.raw (.inl b)) s = {Outcome.ret 1 b s} := by
  let P := extendModel M.raw (.inl b)
  let Q := extendModel P b
  have agree := (envOfBound_agrees M.raw.bound).extend (.inl b)
  have next := agree.extend b
  let branch : UB.Typed (Φ := Φ) (B :: .coprod B A :: A :: Γ) [A, B] :=
    ⟨.br 1 (.var 0), .br (ℓ := 1) rfl (.var (i := 0) rfl)⟩
  exact (outcomes_of_regionAt M.raw (dispatcher (Γ := Γ) A B) branch agree next
    (case_pure_inl (PureValue.var (O := ops M.raw) 0)) s).trans
    (branch_label_outcomes (Γ := (B :: .coprod B A :: A :: Γ)) (L := [A, B]) Q next (1 : Fin 2) rfl (.var (i := 0) rfl) (.var 0) s)

private theorem dispatch_inr (M : Shape.Model.{u,v,w,x} Φ (A :: Γ)) (a : Value M.raw.α) (s : M.raw.σ) :
    nativeOutcomes (dispatcher (Γ := Γ) A B) (extendModel M.raw (.inr a)) s = {Outcome.ret 0 a s} := by
  let P := extendModel M.raw (.inr a)
  let Q := extendModel P a
  have agree := (envOfBound_agrees M.raw.bound).extend (.inr a)
  have next := agree.extend a
  let branch : UB.Typed (Φ := Φ) (A :: .coprod B A :: A :: Γ) [A, B] :=
    ⟨.br 0 (.var 0), .br (ℓ := 0) rfl (.var (i := 0) rfl)⟩
  exact (outcomes_of_regionAt M.raw (dispatcher (Γ := Γ) A B) branch agree next
    (case_pure_inr (PureValue.var (O := ops M.raw) 0)) s).trans
    (branch_label_outcomes (Γ := (A :: .coprod B A :: A :: Γ)) (L := [A, B]) Q next (0 : Fin 2) rfl (.var (i := 0) rfl) (.var 0) s)

private theorem dispatch_mem (M : Shape.Model.{u,v,w,x} Φ (A :: Γ)) {a : Value M.raw.α}
    (typed : ValueTyped M.atomType a (.coprod B A)) (s : M.raw.σ) (o : Outcome 2 M.raw.α M.raw.σ) :
    o ∈ nativeOutcomes (dispatcher (Γ := Γ) A B) (extendModel M.raw a) s ↔
      tagIterationOutcome o = .ret 0 a s := by
  cases typed with
  | inl typed =>
    rw [dispatch_inl M _ s, Set.mem_singleton_iff]
    cases o with
    | ret i b t =>
      have which : i = 0 ∨ i = 1 := by
        rcases i with ⟨i, hi⟩
        have bound : i = 0 ∨ i = 1 := by omega
        exact bound.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      rcases which with rfl | rfl <;> simp [tagIterationOutcome]
    | fault | diverge => simp [tagIterationOutcome]
  | inr typed =>
    rw [dispatch_inr M _ s, Set.mem_singleton_iff]
    cases o with
    | ret i b t =>
      have which : i = 0 ∨ i = 1 := by
        rcases i with ⟨i, hi⟩
        have bound : i = 0 ∨ i = 1 := by omega
        exact bound.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      rcases which with rfl | rfl <;> simp [tagIterationOutcome]
    | fault | diverge => simp [tagIterationOutcome]

private theorem body_outcomes (M : Shape.Model.{u,v,w,x} Φ (A :: Γ))
    (hr : ValueBranches (A :: Γ) r [.coprod B A]) (s : M.raw.σ) :
    nativeOutcomes (step hr) M.raw s =
      Set.preimage tagIterationOutcome (nativeOutcomes ⟨r, hr.hasType⟩ M.raw s) := by
  have typed : ReturnsTyped (L := [.coprod B A]) M.atomType (WithTop.some (nativeOutcomes ⟨r, hr.hasType⟩ M.raw s)) :=
    returns_typed (.native ⟨r, hr.hasType⟩) M s
  change nativeOutcomes ⟨r.lsubst _, hr.hasType.lsubst dispatch_typed⟩ M.raw s = _
  rw [literal_outcomes hr dispatch_typed]
  ext o
  change (_ ∨ ∃ i a t, Outcome.ret i a t ∈ nativeOutcomes ⟨r, hr.hasType⟩ M.raw s ∧
      o ∈ nativeOutcomes (dispatcher (Γ := Γ) A B) (extendModel M.raw a) t) ↔
    tagIterationOutcome o ∈ nativeOutcomes ⟨r, hr.hasType⟩ M.raw s
  constructor
  · rintro (early | ⟨i, a, t, first, last⟩)
    · cases o with
      | ret => exact early.elim
      | fault | diverge => exact early
    · have shape := typed ⟨WithTop.coe_ne_top, first⟩
      have ei := Fin.eq_zero i
      subst i
      rwa [(dispatch_mem M shape t o).mp last]
  · intro returned
    cases o with
    | fault | diverge => exact .inl returned
    | ret i b t =>
      have shape := typed ⟨WithTop.coe_ne_top, returned⟩
      exact .inr ⟨0, _, t, returned, (dispatch_mem M shape t _).mpr rfl⟩

private abbrev entry (A B : Ty κ) : UB.Typed (Φ := Φ) (A :: Γ) [A, B] :=
  ⟨.br 0 (.var 0), .br (ℓ := 0) rfl (.var (i := 0) rfl)⟩

private abbrev blocks (hr : ValueBranches (A :: Γ) r [.coprod B A]) (i : Fin 1) :
    UB.Typed (Φ := Φ) ([A].get i :: A :: Γ) [A, B] :=
  ⟨(iterationBody r).renameVars (lift Nat.succ),
    by
      rw [Fin.eq_zero i]
      exact (step hr).property.renameVars ((SSA.Ren.wk Γ A).lift A)⟩

theorem native_iterateRegion (M : Shape.Model.{u,v,w,x} Φ Γ) (hr : ValueBranches (A :: Γ) r [.coprod B A])
    (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ) :
    Shape.denote (.native ⟨_, (iterateRegion_valueBranches hr).hasType⟩) (M.extend a.property) s =
      iterateObservations (interpretSingleton M (.native ⟨r, hr.hasType⟩)) a s := by
  let initial := M.extend a.property
  let start := entry (Φ := Φ) (Γ := Γ) A B
  change Silmaril.Isotope.LambdaSSA.UB.Overlay.denote (.native ⟨nativeFeedback (R := [A]) (L := [B]) start (blocks hr),
      nativeFeedback_hasType (R := [A]) (L := [B]) start (blocks hr)⟩)
    initial.raw s = _
  rw [← denote_native_feedback (R := [A]) (L := [B]) start (blocks hr)]
  let f := interpretSingleton M (.native ⟨r, hr.hasType⟩)
  let graph := feedbackRun (R := [A]) (L := [B]) (.native start) (fun i => .native (blocks hr i)) initial.raw
  let target := iterationGraph f a
  change Feedback.close graph (.entry s) = Feedback.close target (.entry s)
  have sameEntry (s₀ : M.raw.σ) : graph (.entry s₀) = target (.entry s₀) := by
    exact congrArg WithTop.some (branch_label_outcomes (M.extend a.property).raw
      ((envOfBound_agrees M.raw.bound).extend a.val) (L := [A, B]) 0 rfl
      (.var (i := 0) rfl) (.var 0) s₀)
  have sameBlock (i : Fin 1) (b : singlePayload (atomType := M.atomType) A) (t : M.raw.σ) :
      graph (.block i b.val t) = target (.block i b.val t) := by
    have ei := Fin.eq_zero i
    subst i
    change WithTop.some (nativeOutcomes (blocks hr 0) (extendModel (extendModel M.raw a.val) b.val) t) =
      (f.total (0 : Fin 1) b.val t).map (Set.preimage tagIterationOutcome)
    rw [Arrow.total_typed f (0 : Fin 1) b t]
    exact congrArg WithTop.some ((lift_outcomes (step hr).property M.raw a.val b.val t (blocks hr 0).property).trans
      (body_outcomes (M.extend b.property) hr t))
  have shaped {p} (path : Feedback.Reaches graph (.entry s) p) :
      match p with
      | .entry _ => True
      | .block _ b _ => ValueTyped M.atomType b A := by
    induction path with
    | refl => trivial
    | @tail p _ _ edge ih =>
      cases edge with
      | @branch i b t run =>
        have ei := Fin.eq_zero i
        subst i
        cases p with
        | entry s₀ =>
          exact (returns_typed (.native (entry (Φ := Φ) (Γ := Γ) A B)) (M.extend a.property) s₀ run)
        | block j c s₀ =>
          have ej := Fin.eq_zero j
          subst j
          exact (returns_typed (.native (blocks hr 0)) ((M.extend a.property).extend ih) s₀ run)
  have same {p} (path : Feedback.Reaches graph (.entry s) p) : graph p = target p := by
    cases p with
    | entry s₀ => exact sameEntry s₀
    | block i b t => exact sameBlock i ⟨b, shaped path⟩ t
  apply Feedback.Bisimulation.close_eq (map := id)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q path edge
    cases edge with | branch run => exact .branch (same path ▸ run)
  · intro p q path edge
    cases edge with | branch run => exact ⟨_, .branch ((same path).symm ▸ run), rfl⟩
  · intro p path
    change (graph p = ⊤ ↔ target p = ⊤)
    rw [same path]
  · intro p path o
    change (graph p).Ordinary _ ↔ (target p).Ordinary _
    rw [same path]

theorem interpretCfgEta_iterateSum (M : Shape.Model.{u,v,w,x} Φ Γ)
    (f : LambdaSSA.Region.CfgEta.TypeCategory.ofType (Φ := Φ) (Γ := Γ) A ⟶
      LambdaSSA.Region.CfgEta.TypeCategory.ofType (.coprod B A)) :
    Shape.Paper.interpretHom M (LambdaSSA.Region.Paper.Hom.ofCfgEta
      (LambdaSSA.Region.CfgEta.TypeCategory.iterateSum f).hom) =
      Shape.Category.iterateSum (Shape.Paper.interpretHom M (LambdaSSA.Region.Paper.Hom.ofCfgEta f.hom)) := by
  obtain ⟨r, hr, rfl⟩ := LambdaSSA.Region.CfgEta.TypeCategory.exists_region f
  rw [LambdaSSA.Region.CfgEta.TypeCategory.iterateSum_ofRegion]
  apply Shape.Category.arrow_ext
  intro i a s
  obtain rfl := Fin.eq_zero i
  exact native_iterateRegion M hr a s

theorem interpret_guarded_feedback (M : Shape.Model.{u,v,w,x} Φ Γ)
    (f : (LambdaSSA.Region.Paper.fromNative (Φ := Φ) (Γ := Γ)).obj (ContinuationContext.single A) ⟶
      LambdaSSA.Region.Paper.fromNative.obj (ContinuationContext.single (.coprod B A))) :
    Shape.Paper.interpretHom M (LambdaSSA.Region.Paper.feedback (X := ContinuationContext.single A)
      (Y := ContinuationContext.single B)
      (f ≫ LambdaSSA.Region.Paper.fromNative.map (LambdaSSA.Region.SyntacticCategory.iterationDispatchHom A B))) =
      Shape.Category.iterateSum (Shape.Paper.interpretHom M f) := by
  obtain ⟨g, hg⟩ := (LambdaSSA.Region.Paper.fromCfgEta (Φ := Φ) (Γ := Γ)).map_surjective f
  have result := interpretCfgEta_iterateSum M (A := A) (B := B) (InducedCategory.homMk g)
  change Shape.Paper.interpretHom M (LambdaSSA.Region.Paper.fromCfgEta.map
      (LambdaSSA.Region.CfgEta.feedback (X := ContinuationContext.single A) (Y := ContinuationContext.single B)
        (g ≫ LambdaSSA.Region.CfgEta.fromNative.map (LambdaSSA.Region.SyntacticCategory.iterationDispatchHom A B)))) =
    Shape.Category.iterateSum (Shape.Paper.interpretHom M (LambdaSSA.Region.Paper.fromCfgEta.map g)) at result
  rw [← LambdaSSA.Region.Paper.feedback_fromCfgEta, Functor.map_comp, hg] at result
  exact result

end Captures

theorem map_iterateSum (M : Shape.Model.{u,v,w,x} Φ [])
    (f : ofType (Φ := Φ) A ⟶ ofType (.coprod B A))
    (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ) :
    ((singletonInterpretation M).map (iterateSum f)).run (0 : Fin 1) a s =
      iterateObservations ((singletonInterpretation M).map f) a s := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  rw [iterateSum_ofRegion]
  exact native_iterateRegion M hr a s

theorem map_ne_top (M : Shape.Model.{u,v,w,x} Φ []) (g : ofType (Φ := Φ) A ⟶ ofType B)
    (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ) :
    ((singletonInterpretation M).map g).run (0 : Fin 1) a s ≠ ⊤ := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion g
  exact WithTop.coe_ne_top

theorem iterateSum_ordinary_iff (M : Shape.Model.{u,v,w,x} Φ [])
    (f : ofType (Φ := Φ) A ⟶ ofType (.coprod B A))
    (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ) (o : Outcome 1 M.raw.α M.raw.σ) :
    (((singletonInterpretation M).map (iterateSum f)).run (0 : Fin 1) a s).Ordinary o ↔
      Feedback.Finite (iterationGraph ((singletonInterpretation M).map f) a) (.entry s) o ∨
      o = .diverge ∧ Feedback.Infinite (iterationGraph ((singletonInterpretation M).map f) a) (.entry s) := by
  have safe : iterateObservations ((singletonInterpretation M).map f) a s ≠ ⊤ :=
    map_iterateSum M f a s ▸ map_ne_top M (iterateSum f) a s
  rw [map_iterateSum, iterateObservations, Feedback.ordinary_close_iff]
  exact and_iff_right (fun h => safe (Feedback.close_eq_top_iff.mpr h))

theorem map_iterateSum_unfold (M : Shape.Model.{u,v,w,x} Φ [])
    (f : ofType (Φ := Φ) A ⟶ ofType (.coprod B A)) :
    (singletonInterpretation M).map (iterateSum f) =
      (singletonInterpretation M).map f ≫
        Shape.Category.sumDesc (𝟙 _) ((singletonInterpretation M).map (iterateSum f)) := by
  let iso := LambdaSSA.Region.Paper.TypeCategory.sumIso (Φ := Φ) B A
  have installed : LambdaSSA.Region.Paper.TypeCategory.iterate (f ≫ iso.hom) = iterateSum f := by
    change iterateSum ((f ≫ iso.hom) ≫ iso.inv) = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have dispatch : iso.hom ≫ coprod.desc (𝟙 (ofType B)) (iterateSum f) =
      (LambdaSSA.Region.Paper.TypeCategory.sumCofanIsColimit B A).desc (BinaryCofan.mk (𝟙 _) (iterateSum f)) := by
    apply BinaryCofan.IsColimit.hom_ext (LambdaSSA.Region.Paper.TypeCategory.sumCofanIsColimit B A)
    · rw [← Category.assoc, LambdaSSA.Region.Paper.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]
      exact ((LambdaSSA.Region.Paper.TypeCategory.sumCofanIsColimit B A).fac
        (BinaryCofan.mk (𝟙 (ofType B)) (iterateSum f)) ⟨WalkingPair.left⟩).symm
    · rw [← Category.assoc, LambdaSSA.Region.Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]
      exact ((LambdaSSA.Region.Paper.TypeCategory.sumCofanIsColimit B A).fac
        (BinaryCofan.mk (𝟙 (ofType B)) (iterateSum f)) ⟨WalkingPair.right⟩).symm
  have step := LambdaSSA.Region.Paper.TypeCategory.iterate_fixpoint (f ≫ iso.hom)
  rw [installed, Category.assoc, dispatch] at step
  have identity := (singletonInterpretation M).map_id (ofType B)
  conv_lhs => rw [step, Functor.map_comp, Shape.Paper.singleton_map_sumDesc, identity]
  rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration
